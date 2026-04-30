//! Calling the L-side `ceiling` free fn on an R-kind Conn should
//! fail to type-check: `R: ImpliesL` is not satisfied.

use connections::conn::{Conn, ConnR, ceiling};

const R_CONN: ConnR<i32, i32> = Conn::new_r(|x| x, |x| x);

fn main() {
    let _ = ceiling(&R_CONN, 0_i32);
}
