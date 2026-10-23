use crate::term_representation::TermRepresentation;

pub fn is_beta_redex<T>(term: &T) -> bool
where
    T: TermRepresentation,
{
    // (\x. M) N
    if let Some((f, _)) = term.as_application() {
        f.is_abstraction()
    } else {
        false
    }
}

pub fn beta_reduce<T>(term: &mut T) -> bool
where
    T: TermRepresentation,
{
    let Some((f, N)) = term.as_application() else {
        return false;
    };

    let Some((x, M)) = f.as_abstraction() else {
        return false;
    };

    let mut new_term = M.clone();
    new_term.substitute(x, N);
    *term = new_term;
    true
}

pub fn normal_order_reduction_iter<T>(term: &mut T) -> bool
where
    T: TermRepresentation,
{
    if is_beta_redex(term) {
        beta_reduce(term);
        true
    } else if let Some((_, b)) = term.as_abstraction_mut() {
        normal_order_reduction_iter(b)
    } else if let Some((m, n)) = term.as_application_mut() {
        normal_order_reduction_iter(m) || normal_order_reduction_iter(n)
    } else {
        false
    }
}

pub fn normal_order_reduction<T>(term: &mut T)
where
    T: TermRepresentation,
{
    loop {
        if !normal_order_reduction_iter(term) {
            break;
        }
    }
}
