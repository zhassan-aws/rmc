// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This test checks that verification succeeds for a `HashSet` created with the default hasher.
//! This used to fail: https://github.com/model-checking/kani/issues/723 until we added a hook for
//! `hashmap_random_keys`

use std::collections::HashSet;

#[kani::proof]
fn check_hashmap() {
    let set = HashSet::<char>::with_capacity(100);
    assert!(set.is_empty());
    assert!(set.capacity() >= 100);
    let x = kani::any();
    assert!(!set.contains(&x));
}
