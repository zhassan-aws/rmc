// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module introduces stubs for alloc methods.

// Export everything else from std::alloc.
pub use std::alloc::*;

use crate::alloc::Layout;
use crate::cmp;
use crate::ptr;

pub unsafe fn realloc(ptr: *mut u8, old_layout: Layout, new_size: usize) -> *mut u8 {
    let new_layout =  Layout::from_size_align(new_size, old_layout.align()).unwrap();
    let new_ptr = alloc(new_layout);
    if !new_ptr.is_null() {
        let size = cmp::min(old_layout.size(), new_size);
        ptr::copy_nonoverlapping(ptr, new_ptr, size);
        dealloc(ptr, old_layout);
    }
    new_ptr
}
