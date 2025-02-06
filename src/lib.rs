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

//! A probabilistic counting data structure that never undercounts items before
//! it hits counter's capacity. It is a table structure with the depth being the
//! number of hashes and the width being the number of unique items. When a key
//! is inserted, each row's hash function is used to generate the index for that
//! row. Then the element's count at that index is incremented. As a result, one
//! key being inserted will increment different indices in each row. Querying the
//! count returns the minimum values of these elements since some hashes might collide.
//!
//!
//! Users are supposed to synchronize concurrent accesses to the data structure.
//!
//! E.g. insert(1)
//! hash1(1) = 2 -> increment row 1, index 2
//! hash2(1) = 5 -> increment row 2, index 5
//! hash3(1) = 3 -> increment row 3, index 3
//! etc.
//!
//! # Usage
//!
//! ```
//! use cmsketch::CMSketchU32;
//!
//! const ERROR: f64 = 0.01;
//! const CONFIDENCE: f64 = 0.95;
//!
//! fn main() {
//!     let mut cms = CMSketchU32::new(ERROR, CONFIDENCE);
//!     for i in 0..10 {
//!         for _ in 0..i {
//!             cms.inc(i);
//!         }
//!     }
//!     
//!     for i in 0..10 {
//!         assert!(cms.estimate(i) >= i as u32);
//!     }
//!     
//!     cms.halve();
//!     
//!     for i in 0..10 {
//!         assert!(cms.estimate(i) >= (i as f64 * 0.5) as u32);
//!     }
//! }
//! ```

mod base;
pub use base::*;

mod atomic;
pub use atomic::*;
