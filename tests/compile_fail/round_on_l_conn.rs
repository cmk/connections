//! Calling `round(...)` on a one-sided L-Conn should fail to
//! type-check: `round` takes `&T: ConnK<A, B>` (= `ConnL + ConnR`),
//! and a bare `Conn<_, _, L>` is not a `ConnK`.

use connections::conn::Conn;
use connections::round;

const L_CONN: Conn<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _: i32 = round(&L_CONN, 0_i32);
}
