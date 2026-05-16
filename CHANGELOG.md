# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## [0.1.2] - 2026-05-16

### Fixed
- Fixed Miri-detected Undefined Behavior in `try_from_*` functions of `NtUnicodeStrMut` ([#2])
- Fixed warnings emitted by latest Rust 1.95.0

[#2]: https://github.com/ColinFinck/nt-string/pull/2


## [0.1.1] - 2023-06-13

### Added
- Added `U16StrLe::u16_iter` as a public function


## [0.1.0] - 2023-05-31
- Initial release
