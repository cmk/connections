//! Calling `.ceil(...)` on an R-kind Conn should fail to
//! type-check: `ceil` is an inherent method only on
//! `Conn<_, _, L>`, so the method lookup on `Conn<i32, i32, R>`
//! finds nothing.

use connections::conn::{Conn, R};

const R_CONN: Conn<i32, i32, R> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _ = R_CONN.ceil(0_i32);
}
