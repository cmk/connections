//! Calling `.floor(...)` on an L-kind Conn should fail to type-check:
//! `floor` is an inherent method only on `Conn<_, _, R>`, so the
//! method lookup on `Conn<i32, i32, L>` finds nothing.

use connections::conn::Conn;

const L_CONN: Conn<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _ = L_CONN.floor(0_i32);
}
