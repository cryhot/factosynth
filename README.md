
# Factosynth
[![Python package](https://github.com/cryhot/factosynth/actions/workflows/pythonpackage.yaml/badge.svg)](https://github.com/cryhot/factosynth/actions/workflows/pythonpackage.yaml)

_A [circuit network](https://wiki.factorio.com/Circuit_network) synthesizer for [Factorio](https://www.factorio.com/)._

---


## Installation

List of dependencies:
- python libraries listed in [`requirements.txt`](requirements.txt)


## Examples

See [`examples.ipynb`](examples.ipynb) notebook.


## Tests

Run `python3 -m pytest`.
Alternatively, run directly `tests/test_behavior.py`.


## See also

The [Cnide](https://github.com/charredutensil/cnide) project ([website](https://charredutensil.github.io/cnide/)) proposed the syntax to represent circuit networks as textual programs.

In Cnide, decider combinators with `first`, `second` and `output` signals, and comparator `⋈` := `>`|`<`|`=`|`≥`|`≤`|`≠`, has the syntax:
```
first ⋈ second then output
```
If using the "1" behavior instead of the "input count" behavior, the syntax is:
```
first ⋈ second then 1 as output
```

In Cnide, arithmetic combinators with `first`, `second` and `output` signals, and operation `⊠` := `*`|`/`|`+`|`-`|`%`|`^`|`<<`|`>>`|`AND`|`OR`|`XOR`, has the syntax:
```
first ⊠ second as output
```