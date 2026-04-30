//! Calling `round(...)` on a one-sided L-Conn should fail to
//! type-check: `round` takes `&T: Triple<A, B>` (= `ViewL + ViewR`),
//! and a bare `Conn<_, _, L>` is not a `Triple`.

use connections::conn::{Conn, ConnL};
use connections::round;

const L_CONN: ConnL<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _: i32 = round(&L_CONN, 0_i32);
}
