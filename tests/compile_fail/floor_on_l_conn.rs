//! Calling `floor(&l_conn, ...)` on an L-kind Conn should fail to
//! type-check: `floor` requires `ConnR`, and `Conn<i32, i32, L>`
//! only implements `ConnL`.

use connections::conn::Conn;

const L_CONN: Conn<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _ = connections::conn::floor(&L_CONN, 0_i32);
}
