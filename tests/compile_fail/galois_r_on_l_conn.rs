//! Driving `galois_r` over an L-kind Conn should fail to
//! type-check: the predicate's `K: ImpliesR` bound rejects L.

use connections::conn::{Conn, ConnL};
use connections::prop::conn::galois_r;

const L_CONN: ConnL<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _ = galois_r(&L_CONN, 0_i32, 0_i32);
}
