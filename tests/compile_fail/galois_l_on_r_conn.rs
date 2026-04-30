//! Driving `galois_l` over an R-kind Conn should fail to
//! type-check: the predicate's `K: ImpliesL` bound rejects R.

use connections::conn::{Conn, ConnR};
use connections::prop::conn::galois_l;

const R_CONN: ConnR<i32, i32> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _ = galois_l(&R_CONN, 0_i32, 0_i32);
}
