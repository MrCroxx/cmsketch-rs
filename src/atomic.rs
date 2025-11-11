//  Copyright 2023 MrCroxx
//
//  Licensed under the Apache License, Version 2.0 (the "License");
//  you may not use this file except in compliance with the License.
//  You may obtain a copy of the License at
//
//  http://www.apache.org/licenses/LICENSE-2.0
//
//  Unless required by applicable law or agreed to in writing, software
//  distributed under the License is distributed on an "AS IS" BASIS,
//  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  See the License for the specific language governing permissions and
//  limitations under the License.

use std::sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, AtomicUsize, Ordering};

/// Reduce two 64-bit hashes into one.
///
/// Ported from CacheLib, which uses the `Hash128to64` function from Google's city hash.
#[inline(always)]
fn combine_hashes(upper: u64, lower: u64) -> u64 {
    const MUL: u64 = 0x9ddfea08eb382d69;

    let mut a = (lower ^ upper).wrapping_mul(MUL);
    a ^= a >> 47;
    let mut b = (upper ^ a).wrapping_mul(MUL);
    b ^= b >> 47;
    b = b.wrapping_mul(MUL);
    b
}

#[inline(always)]
fn twang_mix64(val: u64) -> u64 {
    let mut val = (!val).wrapping_add(val << 21); // val *= (1 << 21); val -= 1
    val = val ^ (val >> 24);
    val = val.wrapping_add(val << 3).wrapping_add(val << 8); // val *= 1 + (1 << 3) + (1 << 8)
    val = val ^ (val >> 14);
    val = val.wrapping_add(val << 2).wrapping_add(val << 4); // va; *= 1 + (1 << 2) + (1 << 4)
    val = val ^ (val >> 28);
    val = val.wrapping_add(val << 31); // val *= 1 + (1 << 31)
    val
}

macro_rules! cmsketch {
    ($( {$type:ty, $atomic:ty, $sketch:ident}, )*) => {
        $(
            #[doc = concat!(
                "Count-Min Sketch that stores `",
                stringify!($type),
                "` counters using atomics for concurrent updates.\n\n",
                "Each bucket is backed by [`",
                stringify!($atomic),
                "`], allowing lock-free increments and decrements."
            )]
            #[derive(Debug)]
            pub struct $sketch {
                width: usize,
                depth: usize,

                table: Box<[$atomic]>,
            }

            impl $sketch {
                /// Creates a new atomic sketch sized by error `eps` and `confidence`.
                ///
                /// See [`CMSketchU32::new`](crate::CMSketchU32::new) for the mapping between
                /// confidence and depth.
                ///
                /// # Panics
                ///
                /// Panics if `eps <= 0.0` or `confidence <= 0.0`.
                pub fn new(eps: f64, confidence: f64) ->Self {

                    let width = (2.0 / eps).ceil() as usize;
                    let depth = (- (1.0 - confidence).log2()).ceil() as usize;
                    debug_assert!(width > 0, "width: {width}");
                    debug_assert!(depth > 0, "depth: {depth}");

                    let table = std::iter::repeat_with(|| <$atomic>::new(0)).take(width * depth).collect();

                    Self {
                        width,
                        depth,
                        table,
                    }
                }

                /// Atomically increments the count associated with `hash` by 1.
                pub fn inc(&self, hash: u64) {
                    self.inc_by(hash, 1);
                }

                /// Atomically increments the count associated with `hash` by `count`.
                ///
                /// Saturates at the maximum value representable by the counter type and leaves the bucket unchanged
                /// if the update would overflow.
                pub fn inc_by(&self, hash: u64, count: $type) {
                    for depth in 0..self.depth {
                        let index = self.index(depth, hash);
                        let _ = self.table[index].fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| {
                            if x <= <$type>::MAX - count { Some(x + count) } else { None }
                        });
                    }
                }

                /// Atomically decrements the count associated with `hash` by 1.
                pub fn dec(&self, hash: u64) {
                    self.dec_by(hash, 1);
                }

                /// Atomically decrements the count associated with `hash` by `count`.
                ///
                /// Leaves the counter unchanged if it would underflow.
                pub fn dec_by(&self, hash: u64, count: $type) {
                    for depth in 0..self.depth {
                        let index = self.index(depth, hash);
                        let _ = self.table[index].fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| {
                            if x >= count { Some(x - count) } else { None }
                        });
                    }
                }

                /// Returns the minimum counter across all rows for `hash`.
                pub fn estimate(&self, hash: u64) -> $type {
                    unsafe {
                        (0..self.depth).map(|depth| self.table[self.index(depth, hash)].load(Ordering::Relaxed)).min().unwrap_unchecked()
                    }
                }

                /// Resets all counters to zero.
                pub fn clear(&self) {
                    self.table.iter().for_each(|v| v.store(0, Ordering::Relaxed));
                }

                /// Divides every counter by two using an atomic fetch-update.
                pub fn halve(&self) {
                    self.table.iter().for_each(|v| {
                        let _ = v.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| Some(x >> 1));
                    });
                }

                /// Applies a floating-point decay factor to every counter.
                pub fn decay(&self, decay: f64) {
                    self.table.iter().for_each(|v| {
                        let _ = v.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |x| Some((x as f64 * decay) as $type));
                    });
                }

                /// Returns the configured table width (number of columns).
                pub fn width(&self) -> usize {
                    self.width
                }

                /// Returns the number of hash rows.
                pub fn depth(&self) -> usize {
                    self.depth
                }

                /// Returns the maximum representable counter for this sketch.
                pub fn capacity(&self) -> $type {
                    <$type>::MAX
                }

                #[inline(always)]
                fn index(&self, depth: usize, hash: u64) -> usize {
                    depth * self.width
                        + (combine_hashes(twang_mix64(depth as u64), hash) as usize % self.width)
                }

                /// Returns the amount of memory used by the sketch in bytes.
                pub fn memory(&self) -> usize {
                    (<$type>::BITS as usize * self.depth * self.width + usize::BITS as usize * 3) / 8
                }
            }
        )*
    };
}

cmsketch! {
    {u8, AtomicU8, CMSketchAtomicU8},
    {u16, AtomicU16, CMSketchAtomicU16},
    {u32, AtomicU32, CMSketchAtomicU32},
    {u64, AtomicU64, CMSketchAtomicU64},
    {usize, AtomicUsize, CMSketchAtomicUsize},
}

macro_rules! test_cmsketch {
    ($( {$module:ident, $type:ty, $atomic:ty, $sketch:ident}, )*) => {
        $(
            #[cfg(test)]
            mod $module {
                use itertools::Itertools;
                use rand_mt::Mt64;

                use super::*;

                #[test]
                fn test_new() {
                    let cms = $sketch::new(0.01, 0.5);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 1);

                    let cms = $sketch::new(0.01, 0.6);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 2);

                    let cms = $sketch::new(0.01, 0.7);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 2);

                    let cms = $sketch::new(0.01, 0.8);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 3);

                    let cms = $sketch::new(0.01, 0.9);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 4);

                    let cms = $sketch::new(0.01, 0.95);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 5);

                    let cms = $sketch::new(0.01, 0.995);
                    assert_eq!(cms.width(), 200);
                    assert_eq!(cms.depth(), 8);
                }

                #[test]
                #[should_panic]
                fn test_new_with_invalid_args() {
                    $sketch::new(0.0, 0.0);
                }

                #[test]
                fn test_inc() {
                    let cms = $sketch::new(0.01, 0.9);

                    let mut rng = Mt64::new_unseeded();
                    let keys = (0..100).map(|_| rng.next_u64()).collect_vec();

                    for i in 0..100 {
                        for _ in 0..i {
                            cms.inc(keys[i]);
                        }
                    }

                    for i in 0..100 {
                        assert!(
                            cms.estimate(keys[i]) >= std::cmp::min(i as $type, cms.capacity()),
                            "assert {} >= {} failed",
                            cms.estimate(keys[i]), std::cmp::min(i as $type, cms.capacity())
                        );
                    }
                }

                #[test]
                fn test_dec() {
                    let cms = $sketch::new(0.01, 0.9);

                    let mut rng = Mt64::new_unseeded();
                    let keys = (0..100).map(|_| rng.next_u64()).collect_vec();


                    for i in 0..100 {
                        for _ in 0..i {
                            cms.inc(keys[i]);
                        }
                    }

                    for i in 0..100 {
                        for _ in 0..i {
                            cms.dec(keys[i]);
                        }
                    }

                    for i in 0..100 {
                        assert_eq!(cms.estimate(keys[i]), 0);
                    }
                }

                #[test]
                fn test_clear() {
                    let cms = $sketch::new(0.01, 0.9);

                    let mut rng = Mt64::new_unseeded();
                    let keys = (0..100).map(|_| rng.next_u64()).collect_vec();

                    for i in 0..100 {
                        for _ in 0..i {
                            cms.inc(keys[i]);
                        }
                    }

                    cms.clear();

                    for i in 0..100 {
                        assert_eq!(cms.estimate(keys[i]), 0);
                    }
                }

                #[test]
                fn test_halve() {
                    let cms = $sketch::new(0.01, 0.9);

                    let mut rng = Mt64::new_unseeded();
                    let keys = (0..1000).map(|_| rng.next_u64()).collect_vec();

                    for i in 0..1000 {
                        for _ in 0..i {
                            cms.inc(keys[i]);
                        }
                    }


                    for i in 0..1000 {
                        assert!(
                            cms.estimate(keys[i]) >= std::cmp::min(i as $type, cms.capacity()),
                            "assert {} >= {} failed",
                            cms.estimate(keys[i]), std::cmp::min(i as $type, cms.capacity())
                        );
                    }

                    cms.halve();

                    for i in 0..1000 {
                        assert!(
                            cms.estimate(keys[i]) >= std::cmp::min(i as $type / 2, cms.capacity()),
                            "assert {} >= {} failed",
                            cms.estimate(keys[i]), std::cmp::min(i as $type / 2, cms.capacity())
                        );
                    }
                }

                #[test]
                fn test_decay() {
                    let cms = $sketch::new(0.01, 0.9);
                    let mut rng = Mt64::new_unseeded();
                    let keys = (0..1000).map(|_| rng.next_u64()).collect_vec();

                    for i in 0..1000 {
                        for _ in 0..i {
                            cms.inc(keys[i]);
                        }
                    }

                    for i in 0..1000 {
                        assert!(
                            cms.estimate(keys[i]) >= std::cmp::min(i as $type, cms.capacity()),
                            "assert {} >= {} failed",
                            cms.estimate(keys[i]), std::cmp::min(i as $type, cms.capacity())
                        );
                    }

                    const FACTOR: f64 = 0.5;
                    cms.decay(FACTOR);

                    for i in 0..1000 {
                        assert!(cms.estimate(keys[i]) >= (std::cmp::min(i as $type, cms.capacity()) as f64 * FACTOR).floor() as $type);
                    }
                }

                #[test]
                fn test_collisions() {
                    let cms = $sketch::new(0.01, 0.9);
                    let mut rng = Mt64::new_unseeded();
                    let keys = (0..1000).map(|_| rng.next_u64()).collect_vec();
                    let mut sum = 0;

                    // Try inserting more keys than cms table width
                    for i in 0..1000 {
                        for _ in 0..i {
                            cms.inc(keys[i]);
                        }
                        sum += i;
                    }

                    let error = sum as f64 * 0.01;
                    for i in 0..10 {
                        assert!(cms.estimate(keys[i]) >= i as $type);
                        assert!(i as f64 + error >= cms.estimate(keys[i]) as f64);
                    }
                }
            }
        )*
    }
}

test_cmsketch! {
    {tests_cmsketch_atomic_u8, u8, AtomicU8, CMSketchAtomicU8},
    {tests_cmsketch_atomic_u16, u16, AtomicU16, CMSketchAtomicU16},
    {tests_cmsketch_atomic_u32, u32, AtomicU32, CMSketchAtomicU32},
    {tests_cmsketch_atomic_u64, u64, AtomicU64, CMSketchAtomicU64},
    {tests_cmsketch_atomic_usize, usize, AtomicUsize, CMSketchAtomicUsize},
}
