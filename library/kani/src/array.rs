// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::Arbitrary;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

#[inline(never)]
#[rustc_diagnostic_item = "KaniAnyArray"]
pub fn any_array<T>() -> Array<T>
where
    T: Arbitrary,
{
    #[allow(clippy::empty_loop)]
    loop {}
}

pub struct Array<T> {
    _p: PhantomData<T>,
    len: usize,
}

impl<T> Array<T>
where
    T: Arbitrary,
{
    #[inline(never)]
    #[rustc_diagnostic_item = "KaniAnyArrayLen"]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(never)]
    #[rustc_diagnostic_item = "KaniAnyArraySet"]
    pub fn set(&mut self, _index: usize, _value: T) {}

    #[inline(never)]
    #[rustc_diagnostic_item = "KaniAnyArrayGet"]
    pub fn get(&self, _index: usize) -> T {
        #[allow(clippy::empty_loop)]
        loop {}
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Index<usize> for Array<T> {
    type Output = T;

    #[inline(never)]
    #[rustc_diagnostic_item = "KaniAnyArrayIndex"]
    fn index(&self, _index: usize) -> &Self::Output {
        #[allow(clippy::empty_loop)]
        loop {}
    }
}

impl<T> IndexMut<usize> for Array<T> {
    #[inline(never)]
    #[rustc_diagnostic_item = "KaniAnyArrayIndexMut"]
    fn index_mut(&mut self, _index: usize) -> &mut Self::Output {
        #[allow(clippy::empty_loop)]
        loop {}
    }
}
