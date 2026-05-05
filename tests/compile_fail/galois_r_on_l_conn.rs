//! Driving `galois_r` over an L-kind Conn should fail to
//! type-check: the predicate takes `&Conn<_, _, R>`.

use connections::conn::Conn;
use connections::prop::conn::galois_r;

const L_CONN: Conn<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _ = galois_r(&L_CONN, 0_i32, 0_i32);
}
