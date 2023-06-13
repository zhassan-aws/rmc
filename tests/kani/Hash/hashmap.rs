// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This test checks that verification succeeds for a `HashMap` created with the default hasher.
//! This used to fail: https://github.com/model-checking/kani/issues/723 until we added a hook for
//! `hashmap_random_keys`

use std::collections::HashMap;

#[kani::proof]
fn check_hashmap() {
    let map = HashMap::<i32, i32>::new();
    assert!(map.is_empty());
    let x = kani::any();
    assert_eq!(map.get(&x), None);
}
