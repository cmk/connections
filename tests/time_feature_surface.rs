#![cfg(feature = "time")]
#![forbid(unsafe_code)]

use connections::extended::Extended;
use connections::time::{ODTMSECS, SDURU064};
use std::time::Duration as StdDuration;
use time::{Duration, OffsetDateTime};

#[test]
fn time_feature_enables_time_conn_surface() {
    let at = OffsetDateTime::UNIX_EPOCH + Duration::seconds(1);
    assert_eq!(connections::conn::ceil(&ODTMSECS, Extended::Finite(at)), 1);

    let ttl = StdDuration::from_secs(1);
    assert_eq!(
        connections::conn::ceil(&SDURU064, Extended::Finite(ttl)),
        Extended::Finite(1)
    );
}
