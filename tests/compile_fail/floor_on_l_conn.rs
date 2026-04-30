//! Calling the R-side `floor` free fn on an L-kind Conn should fail
//! to type-check: `L: ImpliesR` is not satisfied.

use connections::conn::{Conn, ConnL, floor};

const L_CONN: ConnL<i32, i32> = Conn::new_l(|x| x, |x| x);

fn main() {
    let _ = floor(&L_CONN, 0_i32);
}
