# cmsketch

A count min sketch implementation in Rust.

Ported from [Facebook/CacheLib](https://github.com/facebook/cachelib).

## Usage

```rust
use cmsketch::CMSketchU32;

const ERROR: f64 = 0.01;
const PROBABILITY: f64 = 0.95;
const MAX_WIDTH: usize = 0; // no limits
const MAX_DEPTH: usize = 0; // no limits

fn main() {
    let mut cms = CMSketchU32::new(ERROR, PROBABILITY, MAX_WIDTH, MAX_DEPTH);
    
    for i in 0..10 {
        for _ in 0..i {
            cms.add(i);
        }
    }
    
    for i in 0..10 {
        assert!(cms.count(i) >= i as u32);
    }
    
    cms.decay(0.5);
    
    for i in 0..10 {
        assert!(cms.count(i) >= (i as f64 * 0.5) as u32);
    }
}
```

## Roadmap

- [] more key type support
- [] benchmark