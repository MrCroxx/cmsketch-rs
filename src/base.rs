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
    ($( {$type:ty, $sketch:ident}, )*) => {
        $(
            #[doc = concat!(
                "Count-Min Sketch storing non-atomic `",
                stringify!($type),
                "` counters.\n\n",
                "Use [`", stringify!($sketch), "::new`] to size the table based on error ",
                "(`eps`) and confidence requirements."
            )]
            #[derive(Debug)]
            pub struct $sketch {
                width: usize,
                depth: usize,

                table: Box<[$type]>,
            }

            impl $sketch {
                /// Creates a new sketch sized by the target error `eps` and confidence.
                ///
                /// `eps` controls the maximum additive error (≈ `2/width`), while
                /// `confidence` determines the number of hash rows (depth).
                ///
                /// Typical confidence to depth mapping:
                ///
                /// ```text
                /// 0.50 => 1 row
                /// 0.80 => 3 rows
                /// 0.95 => 5 rows
                /// 0.995 => 8 rows
                /// ```
                ///
                /// # Panics
                ///
                /// Panics if `eps <= 0.0` or `confidence <= 0.0`.
                pub fn new(eps: f64, confidence: f64) ->Self {

                    let width = (2.0 / eps).ceil() as usize;
                    let depth = (- (1.0 - confidence).log2()).ceil() as usize;
                    let table = {
                        // Use `resize` instead of `vec![]` to avoid page faults caused by delayed allocation.
                        let mut data = Vec::with_capacity(width * depth);
                        data.resize(width * depth, 0);
                        data.into_boxed_slice()
                    };

                    debug_assert!(width > 0, "width: {width}");
                    debug_assert!(depth > 0, "depth: {depth}");
                    debug_assert_eq!(table.len(), width * depth);

                    Self {
                        width,
                        depth,
                        table,
                    }
                }

                /// Increments the count associated with the provided hash by 1.
                pub fn inc(&mut self, hash: u64) {
                    self.inc_by(hash, 1);
                }

                /// Increments the count associated with the provided hash by `count`.
                ///
                /// Saturates at the maximum value representable by the counter type.
                pub fn inc_by(&mut self, hash: u64, count: $type) {
                    for depth in 0..self.depth {
                        let index = self.index(depth, hash);
                        self.table[index] = self.table[index].saturating_add(count);
                    }
                }

                /// Decrements the count associated with the provided hash by 1.
                pub fn dec(&mut self, hash: u64) {
                    self.dec_by(hash, 1);
                }

                /// Decrements the count associated with the provided hash by `count`.
                ///
                /// Saturates at zero if the counter would go negative.
                pub fn dec_by(&mut self, hash: u64, count: $type) {
                    for depth in 0..self.depth {
                        let index = self.index(depth, hash);
                        self.table[index] = self.table[index].saturating_sub(count);
                    }
                }

                /// Returns the minimum counter across all rows for `hash`.
                ///
                /// This is the standard Count-Min Sketch estimator and forms an upper bound.
                pub fn estimate(&self, hash: u64) -> $type {
                    unsafe {
                        (0..self.depth).map(|depth| self.table[self.index(depth, hash)]).min().unwrap_unchecked()
                    }
                }

                /// Resets all counters to zero.
                pub fn clear(&mut self) {
                    self.table.iter_mut().for_each(|c| *c = 0);
                }

                /// Divides every counter by two using a right shift.
                ///
                /// Useful for exponential decay where counts represent recent activity.
                pub fn halve(&mut self) {
                    self.table.iter_mut().for_each(|c| *c >>= 1);
                }

                /// Multiplies every counter by `decay` and truncates back into `$type`.
                ///
                /// Values are floored after multiplication; choose `decay` in `(0, 1]`.
                pub fn decay(&mut self, decay: f64) {
                    self.table.iter_mut().for_each(|c| *c = (*c as f64 * decay) as $type);
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

                /// Returns the amount of memory the sketch uses in bytes.
                pub fn memory(&self) -> usize {
                    (<$type>::BITS as usize * self.depth * self.width + usize::BITS as usize * 3) / 8
                }
            }
        )*
    };
}

cmsketch! {
    {u8, CMSketchU8},
    {u16, CMSketchU16},
    {u32, CMSketchU32},
    {u64, CMSketchU64},
    {usize, CMSketchUsize},
}

macro_rules! test_cmsketch {
    ($( {$module:ident, $type:ty, $sketch:ident}, )*) => {
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
                    let mut cms = $sketch::new(0.01, 0.9);

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
                    let mut cms = $sketch::new(0.01, 0.9);

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
                    let mut cms = $sketch::new(0.01, 0.9);

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
                    let mut cms = $sketch::new(0.01, 0.9);

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
                    let mut cms = $sketch::new(0.01, 0.9);
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
                    let mut cms = $sketch::new(0.01, 0.9);
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
    };
}

test_cmsketch! {
    {tests_u8, u8, CMSketchU8},
    {tests_u16, u16, CMSketchU16},
    {tests_u32, u32, CMSketchU32},
    {tests_u64, u64, CMSketchU64},
    {tests_usize, usize, CMSketchUsize},
}
