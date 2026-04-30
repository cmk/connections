//! Calling `.ceiling(...)` on an R-kind Conn should fail to
//! type-check: `ceiling` is an inherent method only on
//! `Conn<_, _, L>`, so the method lookup on `Conn<i32, i32, R>`
//! finds nothing.

use connections::conn::{Conn, ConnR};

const R_CONN: ConnR<i32, i32> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _ = R_CONN.ceiling(0_i32);
}
