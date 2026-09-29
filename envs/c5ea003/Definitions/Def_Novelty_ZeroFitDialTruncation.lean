-- Prove2me | Definitions.Def_Novelty_ZeroFitDialTruncation
-- name    : Novelty_ZeroFitDialTruncation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:56:14.088348+00:00
-- url     : https://prove2.me/theorems/8c77ba59-c35d-47b3-931f-c940f8b5c4b2
-- title:
--   Aether Catalog definitions — Novelty_ZeroFitDialTruncation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ZeroFitDialTruncation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ZeroFitDialTruncation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64

/-!
# Truncated zero-count statistics cannot explain the U64 dial

Cycle 3 of the round-61 investigation.

Cycle 1 (`Novelty.ZeroFitDialU64`) showed that the *full* 2-adic tie profile has ceiling
`ρ² → 6/7`, far above the recorded `ρ² = 0.419904`, and that the ceiling is essentially
constant in the bitlen.  A natural rescue for a "the statistic is to blame" explanation is
**truncation**: real instrumentation caps the trailing-zero count at some `c`, merging all
draws with `v₂ ≥ c` (and the draw `0`) into one big block.  Since a big block destroys a lot
of rank variance, one might hope that a small cap explains the low reading.

This file computes that ceiling exactly and refutes the hope:

`ρ²(b, c) = (6/7) · (8^b − 8^{b−c}) / (8^b − 2^b)`  (`capped_spearmanSq`)

which is **increasing in the cap** and bounded below by `3/4` for every cap `c ≥ 1`
(`capped_ge_three_quarters`).  Since the recorded pooled reading is `ρ² = 0.419904 < 3/4`,
*no* truncation of the zero-count statistic can produce it (`no_truncation_explains_u64`).

Two consistency checks fall out.  At `c = 1` the profile is the even/odd split and the
formula gives `(3/4)·2^{2b}/(2^{2b} − 1)`, matching the balanced two-class value
`3jk/((j+k)² − 1)` of `Novelty.ZeroFitDialNested`.  At `c = b` it reproduces the full
dyadic ceiling of cycle 1.

Conclusion of the three cycles: the decline of the zero-fit dial is a property of the
*response*, not of the zero-count statistic, however that statistic is quantised.
-/

open Finset

namespace Catalog.Novelty.ZeroFitDialTruncation

open Catalog.Novelty.ZeroFitDialU64

/-- Tie profile of the trailing-zero count on `{0, …, 2^m − 1}` capped at `c`:
blocks `2^{m−1}, 2^{m−2}, …, 2^{m−c}` and one merged tail block of size `2^{m−c}`. -/
def capped : ℕ → ℕ → List ℕ
  | m, 0 => [2 ^ m]
  | 0, _ + 1 => [1]
  | m + 1, c + 1 => 2 ^ m :: capped m c








end Catalog.Novelty.ZeroFitDialTruncation


