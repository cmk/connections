//! Driving `galois_l` over an R-kind Conn should fail to
//! type-check: the predicate takes `&Conn<_, _, L>`.

use connections::conn::{Conn, R};
use connections::prop::conn::galois_l;

const R_CONN: Conn<i32, i32, R> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _ = galois_l(&R_CONN, 0_i32, 0_i32);
}
