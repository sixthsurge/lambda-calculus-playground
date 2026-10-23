use std::{
    error::Error,
    fmt::{write, Debug, Display},
    str::FromStr,
};

use num_bigint::{BigInt, BigUint};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::{
    term_parsing::{Parse, ParseError, Parser, Token},
    term_representation::{Name, TermRepresentation},
};

pub trait IsTypeSystem: Sized + Clone + Copy + Debug + PartialEq + Eq {
    type Type: IsType<Self>;
    type TypeError: Error + Send + Sync + Clone + Debug;
    type Constant: IsConstant<Self>;

    fn typecheck<Term>(
        term: &Term,
        context: &TypingContext<Self>,
    ) -> Result<Self::Type, Self::TypeError>
    where
        Term: TermRepresentation<Self>;

    /// Try to perform constant evaluation rules such as `succ c -> c+1`.
    fn try_eval_const<Term>(term: &Term) -> Option<Term>
    where
        Term: TermRepresentation<Self>;
}

pub trait IsType<TypeSystem>: Sized + Clone + Debug + PartialEq + Eq + Display + Parse
where
    TypeSystem: IsTypeSystem,
{
}

pub trait IsConstant<TypeSystem>: Sized + Clone + Debug + PartialEq + Eq + Display + Parse
where
    TypeSystem: IsTypeSystem,
{
    /// Returns the type of this constant.
    fn ty(&self) -> TypeSystem::Type;
}

#[derive(Clone, Debug)]
pub struct TypingContext<TypeSystem>(FxHashMap<Name, TypeSystem::Type>)
where
    TypeSystem: IsTypeSystem;

impl<TypeSystem> TypingContext<TypeSystem>
where
    TypeSystem: IsTypeSystem,
{
    pub fn new() -> Self {
        Self(FxHashMap::default())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UntypedLambdaCalculus;

impl IsTypeSystem for UntypedLambdaCalculus {
    type Type = UntypedType;
    type Constant = UntypedConstant;
    type TypeError = UntypedTypeError;

    fn typecheck<Term>(
        term: &Term,
        context: &TypingContext<Self>,
    ) -> Result<Self::Type, Self::TypeError>
    where
        Term: TermRepresentation<Self>,
    {
        Ok(UntypedType::Everything)
    }

    fn try_eval_const<Term>(term: &Term) -> Option<Term>
    where
        Term: TermRepresentation<Self>,
    {
        return None;
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UntypedType {
    Everything,
}

impl Display for UntypedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Everything")
    }
}

impl Parse for UntypedType {
    fn parse(mut parser: Parser) -> Result<(Parser, Self), crate::term_parsing::ParseError> {
        parser.expect(&Token::Name("Everything".into()))?;
        Ok((parser, Self::Everything))
    }
}

impl IsType<UntypedLambdaCalculus> for UntypedType {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UntypedConstant {}

impl UntypedConstant {}

impl Display for UntypedConstant {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        panic!()
    }
}

impl IsConstant<UntypedLambdaCalculus> for UntypedConstant {
    fn ty(&self) -> UntypedType {
        panic!()
    }
}

impl Parse for UntypedConstant {
    fn parse(_: Parser) -> Result<(Parser, Self), crate::term_parsing::ParseError> {
        return Err(ParseError::DoesntExist);
    }
}

#[derive(Clone, Debug, Error)]
pub enum UntypedTypeError {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimplyTypedLambdaCalculus;

impl IsTypeSystem for SimplyTypedLambdaCalculus {
    type Type = SimpleType;
    type Constant = SimpleConstant;
    type TypeError = SimpleTypeError;

    fn typecheck<Term>(
        term: &Term,
        context: &TypingContext<Self>,
    ) -> Result<Self::Type, Self::TypeError>
    where
        Term: TermRepresentation<Self>,
    {
        if let Some(x) = term.as_variable() {
            let name = term.get_name(x);
            if let Some(ty) = context.0.get(&name) {
                Ok(ty.clone())
            } else {
                Err(SimpleTypeError::UnboundVariable(name))
            }
        } else if let Some(c) = term.as_constant() {
            Ok(c.ty())
        } else if let Some((m, n)) = term.as_application() {
            let m_ty = Self::typecheck(m, context)?;
            let n_ty = Self::typecheck(n, context)?;

            match &m_ty {
                SimpleType::Function(a, b) if a.as_ref() == &n_ty => Ok(b.as_ref().clone()),
                _ => Err(SimpleTypeError::BadApplication(m_ty, n_ty)),
            }
        } else if let Some((arg, body, ty)) = term.as_abstraction() {
            let name = term.get_name(arg);
            let binding_ty =
                ty.ok_or_else(|| SimpleTypeError::MissingTypeForBinding(name.clone()))?;
            let mut new_context = context.clone();
            new_context.0.insert(name.clone(), binding_ty.clone());
            let return_ty = Self::typecheck(body, &new_context)?;

            Ok(SimpleType::Function(
                Box::new(binding_ty.clone()),
                Box::new(return_ty),
            ))
        } else {
            panic!("new term dropped")
        }
    }

    fn try_eval_const<Term>(term: &Term) -> Option<Term>
    where
        Term: TermRepresentation<Self>,
    {
        let Some((f, y)) = term.as_application() else {
            return None;
        };
        let Some(SimpleConstant::Int(y)) = y.as_constant() else {
            return None;
        };
        let Some((f, x)) = f.as_application() else {
            return None;
        };
        let Some(SimpleConstant::Int(x)) = x.as_constant() else {
            return None;
        };

        match f.as_constant() {
            Some(SimpleConstant::IAdd) => Some(Term::make_constant(SimpleConstant::Int(x + y))),
            Some(SimpleConstant::IDiv) => Some(Term::make_constant(SimpleConstant::Int(x - y))),
            Some(SimpleConstant::IMul) => Some(Term::make_constant(SimpleConstant::Int(x * y))),
            Some(SimpleConstant::ISub) => Some(Term::make_constant(SimpleConstant::Int(
                x.checked_div(y).unwrap_or(BigInt::ZERO),
            ))),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleType {
    Int,
    Function(Box<SimpleType>, Box<SimpleType>),
}

impl IsType<SimplyTypedLambdaCalculus> for SimpleType {}

impl Display for SimpleType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Function(a, b) => write!(f, "({a} -> {b})"),
        }
    }
}

impl Parse for SimpleType {
    fn parse(mut parser: Parser) -> Result<(Parser, Self), ParseError> {
        let mut ty = if parser.accept(&Token::Name("Int".into())) {
            Self::Int
        } else if parser.accept(&Token::OpenParen) {
            let (new_parser, ty) = Self::parse(parser)?;
            parser = new_parser;
            parser.expect(&Token::CloseParen)?;
            ty
        } else {
            return Err(ParseError::Other("expected Int or (".into()));
        };

        if parser.accept(&Token::Arrow) {
            let (new_parser, right_ty) = Self::parse(parser)?;
            parser = new_parser;
            ty = Self::Function(Box::new(ty), Box::new(right_ty));
        }

        Ok((parser, ty))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimpleConstant {
    Int(BigInt),
    IAdd,
    ISub,
    IMul,
    IDiv,
}

impl IsConstant<SimplyTypedLambdaCalculus> for SimpleConstant {
    fn ty(&self) -> <SimplyTypedLambdaCalculus as IsTypeSystem>::Type {
        match self {
            Self::Int(_) => SimpleType::Int,
            Self::IAdd | Self::ISub | Self::IMul | Self::IDiv => SimpleType::Function(
                Box::new(SimpleType::Int),
                Box::new(SimpleType::Function(
                    Box::new(SimpleType::Int),
                    Box::new(SimpleType::Int),
                )),
            ),
        }
    }
}

impl Display for SimpleConstant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(x) => write!(f, "{x}"),
            Self::IAdd => write!(f, "add"),
            Self::ISub => write!(f, "sub"),
            Self::IMul => write!(f, "mul"),
            Self::IDiv => write!(f, "div"),
        }
    }
}

impl Parse for SimpleConstant {
    fn parse(mut parser: Parser) -> Result<(Parser, Self), ParseError> {
        let name = match parser.peek().cloned() {
            Ok(Token::Name(name)) => {
                parser.next()?;
                Ok(name.clone())
            }
            _ => Err(ParseError::ExpectedSpecificToken(
                Token::Name(Name::from("")),
                parser.peek().ok().cloned(),
            )),
        }?;

        let result = match name.as_str() {
            "add" => Self::IAdd,
            "sub" => Self::IDiv,
            "mul" => Self::IMul,
            "div" => Self::IDiv,
            s => {
                if let Ok(x) = BigInt::from_str(s) {
                    Self::Int(x)
                } else {
                    return Err(ParseError::Other("expected an integer".into()));
                }
            }
        };

        Ok((parser, result))
    }
}

#[derive(Clone, Debug, Error)]
pub enum SimpleTypeError {
    #[error("variable '{0}' is unbound")]
    UnboundVariable(Name),
    #[error("cannot apply {0} to {1}")]
    BadApplication(SimpleType, SimpleType),
    #[error("missing type in binding for '{0}'")]
    MissingTypeForBinding(Name),
}
