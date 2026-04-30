//! Composing an L-kind Conn with an R-kind Conn through `compose_l!`
//! should fail to type-check: the macro's result type is `ConnL`, and
//! the expansion calls `.ceiling()` on each operand — which is a
//! method only on `Conn<_, _, L>`. The R operand has no `.ceiling()`
//! method.

use connections::compose_l;
use connections::conn::{Conn, ConnL, ConnR};

const L_CONN: ConnL<i32, i32> = Conn::new_l(|x| x, |x| x);
const R_CONN: ConnR<i32, i32> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _: ConnL<i32, i32> = compose_l!(L_CONN, R_CONN);
}
