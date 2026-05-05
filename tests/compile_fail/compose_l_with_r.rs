//! Composing an L-kind Conn with an R-kind Conn through `compose_l!`
//! should fail to type-check: the macro's expansion calls `.ceil()`
//! on each operand — which is an inherent method only on
//! `Conn<_, _, L>`. The R operand has no `.ceil()` method.

use connections::compose_l;
use connections::conn::{Conn, R};

const L_CONN: Conn<i32, i32> = Conn::new_l(|x| x, |x| x);
const R_CONN: Conn<i32, i32, R> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _: Conn<i32, i32> = compose_l!(L_CONN, R_CONN);
}
