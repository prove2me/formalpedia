-- Prove2me | Theorems.Thm_Catalog_Novelty_ZeroFitDialTruncation_capped_ge_three_quarters
-- name    : Catalog.Novelty.ZeroFitDialTruncation.capped_ge_three_quarters
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:19:41.762164+00:00
-- url     : https://prove2.me/theorems/69fc221e-0e92-475f-98cb-725dd308d46c
-- title:
--   The truncated ceiling never drops below `3/4`, whatever the cap `c ≥ 1` and bitlen.
-- statement:
--   The truncated ceiling never drops below `3/4`, whatever the cap `c ≥ 1` and bitlen.
--
--   ```lean
--   theorem Catalog.Novelty.ZeroFitDialTruncation.capped_ge_three_quarters(b c : ℕ) (hc1 : 1 ≤ c) (hc : c ≤ b) (hb : 1 ≤ b) :
--       3 / 4 ≤ spearmanSq (capped b c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ZeroFitDialTruncation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ZeroFitDialTruncation.lean#L103

-- Thm stub generated from Novelty/ZeroFitDialTruncation.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialTruncation
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

open Catalog.Novelty.ZeroFitDialTruncation

open Catalog.Novelty.ZeroFitDialU64

theorem Catalog.Novelty.ZeroFitDialTruncation.capped_ge_three_quarters(b c : ℕ) (hc1 : 1 ≤ c) (hc : c ≤ b) (hb : 1 ≤ b) :
    3 / 4 ≤ spearmanSq (capped b c) := by sorry
