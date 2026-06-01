#![cfg(feature = "time")]
#![forbid(unsafe_code)]

use connections::time::{ODTMSECS, SDURU064};
use serde::{Deserialize, Serialize};
use time::serde::rfc3339;
use time::{Duration, OffsetDateTime};

#[derive(Debug, Deserialize, PartialEq, Serialize)]
struct Timestamped {
    #[serde(with = "rfc3339")]
    at: OffsetDateTime,
    #[serde(with = "rfc3339::option")]
    maybe_at: Option<OffsetDateTime>,
}

#[test]
fn time_feature_enables_upstream_time_surface() {
    let _ = ODTMSECS;
    let _ = SDURU064;

    let now: OffsetDateTime = OffsetDateTime::now_utc();
    assert!(now + Duration::seconds(1) > now);

    let value = Timestamped {
        at: OffsetDateTime::UNIX_EPOCH,
        maybe_at: Some(OffsetDateTime::UNIX_EPOCH + Duration::seconds(1)),
    };

    let encoded = serde_json::to_string(&value).expect("RFC3339 serialization should succeed");
    let decoded: Timestamped =
        serde_json::from_str(&encoded).expect("RFC3339 deserialization should succeed");

    assert_eq!(decoded, value);
}
