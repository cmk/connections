//! Composing an L-kind Conn with an R-kind Conn through `compose_l!`
//! should fail to type-check: the macro's expansion calls
//! `ceil(&operand, ...)` on each operand, and the R operand does not
//! implement `ConnL`.

use connections::compose_l;
use connections::conn::{Conn, R};

const L_CONN: Conn<i32, i32> = Conn::new_l(|x| x, |x| x);
const R_CONN: Conn<i32, i32, R> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _: Conn<i32, i32> = compose_l!(L_CONN, R_CONN);
}
