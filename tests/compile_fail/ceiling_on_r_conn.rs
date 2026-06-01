//! Calling `ceil(&r_conn, ...)` on an R-kind Conn should fail to
//! type-check: `ceil` requires `ConnL`, and `Conn<i32, i32, R>`
//! only implements `ConnR`.

use connections::conn::{Conn, R};

const R_CONN: Conn<i32, i32, R> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _ = connections::conn::ceil(&R_CONN, 0_i32);
}
