# Macros for convenient maths with checked, wrapping or saturating semantics

[![crate][crate-image]][crate-link]
[![Docs][docs-image]][docs-link]
![Apache2/MIT licensed][license-image]
![Rust Version][rustc-image]
[![Build Status][build-image]][build-link]

Macromath provides macros which allow to perform checked, wrapping or saturating math
using regular operators (`+-*/%`).

```rust
use macromath::checked;

fn calc() -> Option<i8> {
  Some(100)
}

assert_eq!(Some(50), checked!(calc()? / 2));
assert_eq!(None, checked!(3u32 - 9u32 / 4 * 2));
```

## Minimum Supported Rust Version

This crate currently requires Rust **1.56** or higher.

Minimum supported Rust version can be changed in the future, but it will be
done with a minor version bump.

## SemVer Policy

- All on-by-default features of this library are covered by SemVer
- MSRV is considered exempt from SemVer as noted above

## License

Licensed under either of:

 * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
 * [MIT license](http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.


[//]: # (badges)

[crate-image]: https://img.shields.io/crates/v/macromath.svg
[crate-link]: https://crates.io/crates/macromath
[docs-image]: https://docs.rs/macromath/badge.svg
[docs-link]: https://docs.rs/macromath/
[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[rustc-image]: https://img.shields.io/badge/rustc-1.56+-blue.svg
[build-image]: https://github.com/B4dM4n/macromath-rs/workflows/macromath/badge.svg?branch=main&event=push
[build-link]: https://github.com/B4dM4n/macromath-rs/actions?query=workflow%3Amacromath
