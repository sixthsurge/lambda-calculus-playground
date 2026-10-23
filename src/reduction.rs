use crate::{term_representation::TermRepresentation, type_system::IsTypeSystem};

pub fn is_beta_redex<Term, TypeSystem>(term: &Term) -> bool
where
    TypeSystem: IsTypeSystem,
    Term: TermRepresentation<TypeSystem>,
{
    // (\x. M) N
    if let Some((f, _)) = term.as_application() {
        f.is_abstraction()
    } else {
        false
    }
}

pub fn beta_reduce<Term, TypeSystem>(term: &mut Term) -> bool
where
    TypeSystem: IsTypeSystem,
    Term: TermRepresentation<TypeSystem>,
{
    let Some((f, N)) = term.as_application() else {
        return false;
    };

    let Some((x, M, _)) = f.as_abstraction() else {
        return false;
    };

    let mut new_term = M.clone();
    new_term.substitute(x, N);
    *term = new_term;
    true
}

pub fn normal_order_reduction_iter<Term, TypeSystem>(term: &mut Term) -> bool
where
    TypeSystem: IsTypeSystem,
    Term: TermRepresentation<TypeSystem>,
{
    if let Some(const_eval) = TypeSystem::try_eval_const(term) {
        *term = const_eval;
        true
    } else if is_beta_redex(term) {
        beta_reduce(term);
        true
    } else if let Some((_, b, _)) = term.as_abstraction_mut() {
        normal_order_reduction_iter(b)
    } else if let Some((m, n)) = term.as_application_mut() {
        normal_order_reduction_iter(m) || normal_order_reduction_iter(n)
    } else {
        false
    }
}

pub fn normal_order_reduction<Term, TypeSystem>(term: &mut Term)
where
    TypeSystem: IsTypeSystem,
    Term: TermRepresentation<TypeSystem>,
{
    loop {
        if !normal_order_reduction_iter(term) {
            break;
        }
    }
}
