# cmsketch

A count min sketch implementation in Rust.

Inspired by [Facebook/CacheLib](https://github.com/facebook/cachelib) and [Caffeine](https://github.com/ben-manes/caffeine).

## Usage

Add `cmsketch` into the dependencies of your project: 

```toml
cmsketch = "0.2"
```

```rust
use cmsketch::CMSketchU32;

const ERROR: f64 = 0.01;
const CONFIDENCE: f64 = 0.95;

fn main() {
    let mut cms = CMSketchU32::new(ERROR, CONFIDENCE);
    for i in 0..10 {
        for _ in 0..i {
            cms.inc(i);
        }
    }
    
    for i in 0..10 {
        assert!(cms.estimate(i) >= i as u32);
    }
    
    cms.halve();
    
    for i in 0..10 {
        assert!(cms.estimate(i) >= (i as f64 * 0.5) as u32);
    }
}
```

## MSRV

Rust version >= `1.60.0`.

## Roadmap

- [ ] simd halve
- [ ] benchmark
