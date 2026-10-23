use std::sync::Arc;

use num_bigint::BigUint;
use rustc_hash::FxHashSet;

/// Interface for different representations of lambda terms on which reduction can be performed.
pub trait TermRepresentation : From<CanonicalTerm> + Into<CanonicalTerm> + Clone {
    type VariableId: Clone + Eq + PartialEq + std::hash::Hash;

    /// Capture-avoiding substitution `self <- {N/x} self`.
    fn substitute(&mut self, x: &Self::VariableId, N: &Self);

    fn as_abstraction(&self) -> Option<(&Self::VariableId, &Self)>;
    fn as_application(&self) -> Option<(&Self, &Self)>;
    fn as_variable(&self) -> Option<&Self::VariableId>;
    fn as_abstraction_mut(&mut self) -> Option<(&mut Self::VariableId, &mut Self)>;
    fn as_application_mut(&mut self) -> Option<(&mut Self, &mut Self)>;
    fn as_variable_mut(&mut self) -> Option<&mut Self::VariableId>;

    fn is_abstraction(&self) -> bool { self.as_abstraction().is_some() }
    fn is_application(&self) -> bool { self.as_application().is_some() }
    fn is_variable(&self) -> bool { self.as_variable().is_some() }
}

/// Canonical representation of lambda terms using named variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalTerm {
    Variable(Name),
    Abstraction(Name, Box<CanonicalTerm>),
    Application(Box<CanonicalTerm>, Box<CanonicalTerm>),
}

impl CanonicalTerm {
    pub fn create_church_numeral(value: BigUint) -> Self {
        let f: Name = "f".into();
        let x: Name = "x".into();
        let mut term = CanonicalTerm::Variable(x.clone());

        let mut counter = BigUint::ZERO;
        while counter < value {
            term = CanonicalTerm::Application(Box::new(CanonicalTerm::Variable(f.clone())), Box::new(term));
            counter += BigUint::ONE;
        }

        term = CanonicalTerm::Abstraction(x, Box::new(term));
        term = CanonicalTerm::Abstraction(f, Box::new(term));

        term
    }

    pub fn free_variables(&self) -> FxHashSet<Name> {
        match self {
            Self::Variable(name) => std::iter::once(name).cloned().collect(),
            Self::Abstraction(name, body) => {
                let mut s = body.free_variables();
                s.remove(name);
                s
            }
            Self::Application(m_1, m_2) => m_1
                .free_variables()
                .union(&m_2.free_variables())
                .cloned()
                .collect(),
        }
    }

    pub fn church_numeral_value(&self) -> Option<BigUint> {
        let CanonicalTerm::Abstraction(f, rest) = self else {
            return None;
        };
        let CanonicalTerm::Abstraction(x, rest) = rest.as_ref() else {
            return None;
        };
        let mut rest = rest.as_ref();

        // repeated applications of f.
        let mut f_application_count = BigUint::ZERO;
        while let CanonicalTerm::Application(f_dash, new_rest) = rest {
            let CanonicalTerm::Variable(f_dash_name) = f_dash.as_ref() else {
                return None;
            };
            if f_dash_name != f {
                return None;
            }
            f_application_count += BigUint::ONE;
            rest = new_rest;
        }

        // finally we should have a variable.
        if let CanonicalTerm::Variable(name) = rest
            && name == x
        {
            Some(f_application_count)
        } else {
            None
        }
    }
}

impl TermRepresentation for CanonicalTerm {
    type VariableId = Name;

    fn substitute(&mut self, x: &Self::VariableId, N: &Self) {
        match self {
            Self::Variable(y) => {
                if y == x {
                    *self = N.clone();
                }
            }
            Self::Abstraction(y, M) => {
                if y == x {
                    *y = x.clone();
                } else {
                    let fv_N = N.free_variables();
                    if !fv_N.contains(y) {
                        M.substitute(x, N);
                    } else {
                        // Find fresh variable name.
                        let fv_M = M.free_variables();
                        let y_dash = (0..)
                            .map(|i| Name::from(format!("{}{}", y.as_str(), i)))
                            .find(|name| !fv_N.contains(name) && !fv_M.contains(name))
                            .unwrap();

                        M.substitute(y, &CanonicalTerm::Variable(y_dash.clone()));
                        *y = y_dash;
                        self.substitute(x, N);
                    }
                }
            }
            Self::Application(m1, m2) => {
                m1.substitute(x, N);
                m2.substitute(x, N);
            },
        }   
    }

    fn as_abstraction(&self) -> Option<(&Self::VariableId, &Self)> {
        match self {
            Self::Abstraction(arg, body)  => Some((arg, body.as_ref())),
            _ => None,
        }
    }

    fn as_application(&self) -> Option<(&Self, &Self)> {
        match self {
            Self::Application(m, n) => Some((m.as_ref(), n.as_ref())),
            _ => None,
        }
    }

    fn as_variable(&self) -> Option<&Self::VariableId> {
        match self {
            Self::Variable(name) => Some(name),
            _ => None,
        }
    }

    fn as_abstraction_mut(&mut self) -> Option<(&mut Self::VariableId, &mut Self)> {
        match self {
            Self::Abstraction(arg, body)  => Some((arg, body.as_mut())),
            _ => None,
        }
    }

    fn as_application_mut(&mut self) -> Option<(&mut Self, &mut Self)> {
        match self {
            Self::Application(m, n) => Some((m.as_mut(), n.as_mut())),
            _ => None,
        }   
    }

    fn as_variable_mut(&mut self) -> Option<&mut Self::VariableId> {
        match self {
            Self::Variable(name) => Some(name),
            _ => None,
        }
    }
}

impl std::fmt::Display for CanonicalTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Variable(name) => f.write_str(name.as_str()),
            Self::Abstraction(arg, body) => write!(f, "λ{}.{}", arg.as_str(), &body),
            Self::Application(a, b) => write!(f, "({} {})", &a, &b),
        }
    }
}

/// Variables are identified by De-Bruijn index.
/// Free variables are eliminated prior to conversion by inserting new bindings. (e.g. `a` => `\a. a` => \0)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeBruijnIndexedTerm {
    Variable(i64),
    Abstraction(Box<DeBruijnIndexedTerm>),
    Application(Box<DeBruijnIndexedTerm>, Box<DeBruijnIndexedTerm>),
}

impl From<CanonicalTerm> for DeBruijnIndexedTerm {
    fn from(term: CanonicalTerm) -> Self {
        DeBruijnIndexedTerm::from_canonical(&term, -1, &mut vec![])
    }
}

impl Into<CanonicalTerm> for DeBruijnIndexedTerm {
    fn into(self) -> CanonicalTerm {
        todo!()
    }
}

impl DeBruijnIndexedTerm {
    pub fn from_canonical(term: &CanonicalTerm, binding_depth: i64, bound_variables: &mut Vec<(Name, i64)>) -> Self {
        match term {
            CanonicalTerm::Variable(name) => Self::Variable(
                binding_depth
                    - bound_variables
                        .iter()
                        .position(|(bound_name, _)| name == bound_name)
                        .expect("Term should have no free variables by this point.")
                        as i64,
            ),
            CanonicalTerm::Abstraction(arg, body) => {
                bound_variables.push((arg.clone(), binding_depth));
                let result = Self::Abstraction(Box::new(Self::from_canonical(
                    body.as_ref(),
                    binding_depth + 1,
                    bound_variables,
                )));
                bound_variables.pop();
                result
            }
            CanonicalTerm::Application(m, n) => Self::Application(
                Box::new(Self::from_canonical(m, binding_depth, bound_variables)),
                Box::new(Self::from_canonical(n, binding_depth, bound_variables)),
            ),
        }
    }

    fn substitute(&mut self, n: i64, N: &Self) {
        // http://pl.postech.ac.kr/~gla/pl2007/notes/deBruijn.pdf

        match self {
            Self::Application(M1, M2) => {
                M1.substitute(n, N);
                M2.substitute(n, N);
            }
            Self::Abstraction(M) => {
                M.substitute(n + 1, N);
            }
            &mut Self::Variable(m) => {
                if m < n {
                    *self = Self::Variable(m)
                } else if m == n {
                    *self = N.clone()
                } else {
                    *self = Self::Variable(m - 1)
                }
            }
        }
    }

    pub fn beta_reduce(&mut self) -> bool {
        match self {
            Self::Application(f, N) => {
                if let Self::Abstraction(M) = f.as_ref() {
                    let mut new_self = M.as_ref().clone();
                    new_self.substitute(0, N);
                    *self = new_self;
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

impl std::fmt::Display for DeBruijnIndexedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Variable(index) => write!(f, "{}", index),
            Self::Abstraction(body) => write!(f, "λ {}", body),
            Self::Application(a, b) => write!(f, "({} {})", &a, &b),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name {
    name: Arc<str>,
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

impl Name {
    pub fn as_str(&self) -> &str {
        self.name.as_ref()
    }
}

impl AsRef<str> for Name {
    fn as_ref(&self) -> &str {
        self.name.as_ref()
    }
}

impl From<String> for Name {
    fn from(value: String) -> Self {
        Self {
            name: Arc::from(value),
        }
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Self {
        Self {
            name: Arc::from(value),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cnum_conversion() {
        // Church numeral <-> int.
        for x in [0 as u32, 1, 42].into_iter() {
            assert_eq!(Some(x.into()), CanonicalTerm::create_church_numeral(x.into()).church_numeral_value());
        }
    }
}
