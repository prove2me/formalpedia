-- Prove2me | Theorems.Thm_CompressionLasVegas_avg_description_length_sharp
-- name    : CompressionLasVegas.avg_description_length_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:38:39.268551+00:00
-- url     : https://prove2.me/theorems/e25f2292-ff00-45a4-b1ad-707be677dfc7
-- title:
--   The average-case constant `2` is sharp.
-- statement:
--   **The average-case constant `2` is sharp.**  For the identity decompressor and
--   the set `T` of all strings of length `≤ m` we have, exactly,
--   `∑ K + 2·2^(m+1) = (m+1)·2^(m+1) + 2` while `|T| + 1 = 2^(m+1)`.
--
--   So the average description length of a set of `≈ 2^n` objects can be as small as
--   `n - 2 + o(1)`: the bound `avg_description_length` cannot be improved beyond an
--   additive `O(1)`, and in particular the exponent-counting argument behind it is
--   asymptotically optimal.
--
--   ```lean
--   theorem CompressionLasVegas.avg_description_length_sharp(m : ℕ) :
--       (∑ y ∈ bitStringsUpTo m, K (id : Str → Str) y) + 2 * 2 ^ (m + 1)
--         = (m + 1) * 2 ^ (m + 1) + 2 ∧ (bitStringsUpTo m).card + 1 = 2 ^ (m + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/CompressionLasVegasOWF.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/CompressionLasVegasOWF.lean#L757

-- Thm stub generated from Speculative/AutoResearch/CompressionLasVegasOWF.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
/-
Copyright (c) 2025. All rights reserved.

# Las Vegas compression, average description length, and the one-way boundary

## Overview

This file continues the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: "can random number generators help?").  It builds directly
on `Speculative.AutoResearch.CompressionOneWayFunctions`, which established

* the pigeonhole ceiling `card_le_of_K_le`,
* the **seed-budget** theorem `card_le_of_K_le_seeded` (a randomized decompressor
  with seed space `R` compresses at most `|R| * (2^(s+1) - 1)` objects), and
* the equivalence `owf_iff_compression_hard` between one-way functions and
  hardness of compression search.

The seed-budget theorem charges the compressor for the *whole* seed space: it only
assumes that **some** seed works for each object.  The present file sharpens and
extends that picture in three independent directions.

### 1. It is the success *probability*, not the seed length, that is paid for

`lasVegas_sum_bound` is a double-counting theorem: summing, over a finite target
set `T`, the number of seeds that compress `y` to `s` bits gives at most
`|R| * (2^(s+1) - 1)`.  Consequences:

* `lasVegas_card_bound` : if every `y ∈ T` is compressed by at least `m` seeds
  then `m * |T| ≤ |R| * (2^(s+1) - 1)`, i.e. a Las Vegas compressor with success
  probability `δ = m/|R|` gains at most `log₂(1/δ) + 1` bits — *independently of
  how many random bits it uses*;
* `zero_error_randomness_no_gain` : a randomized compressor that must succeed for
  **every** seed gains exactly nothing (the deterministic ceiling reappears);
* `lasVegas_bound_tight` : the bound is tight within a factor `2`, witnessed by
  the seeded prefix system `prefixSeeded`, where `j` of the `i + j` seed bits are
  "used" and the success probability is exactly `2^(-j)`;
* `lasVegas_incompressible` : for every seeded family and every `k` there is a
  string of length `k + s + 1` whose success probability is below `2^(-k)`.

### 2. Average-case (Shannon-type) lower bounds from pure counting

`layer_lower_bound` is a layer-cake inequality turning any counting bound into a
bound on the *sum* of description lengths.  From it:

* `avg_description_length` : for any decompressor and any set of `2^n` describable
  objects the average description length is at least `n - 2`;
* `avg_description_length_seeded` : with `2^k` seeds the average is still at least
  `n - k - 3`.  So randomness buys at most `k + O(1)` bits *on average*, not just
  in the worst case.

### 3. Las Vegas randomness does not cross the cryptographic boundary

`tryList` is a deterministic simulation of a Las Vegas algorithm: run all seeds
from a finite list and keep the first output that verifies.  For a class closed
under this operation (`LasVegasClass`), a one-way function defeats *every* Las
Vegas algorithm **totally**:

* `owf_defeats_las_vegas` : there is a describable `y` on which **all** seeds fail;
* `owf_defeats_las_vegas_compression` : the same for seeded compression search.

Non-vacuity is checked (`lengthLVClass`, `lengthClass_las_vegas_compression_hard`):
the class of length-nondecreasing algorithms satisfies the new closure axiom and
carries a genuine one-way function.

`compression_randomness_calibration` collects the four regimes into a single
statement.

All results are proved from scratch; there are no axioms and no `sorry`.
-/

open CompressionLasVegas

open CompressionOWF

/-! ## Section 1: Las Vegas compression — the price of a success probability -/


open scoped Classical

variable {α : Type*}









/-! ## Section 2: the Las Vegas bound is tight -/


open scoped Classical






/-! ## Section 3: average description length (Shannon bounds from counting) -/


open scoped Classical

variable {α : Type*}








/-! ## Section 4: Las Vegas algorithms against the cryptographic boundary -/












/-! ### Section 4b: Las Vegas compression search is *equivalent* to inversion

The previous results show that one-way functions block Las Vegas compression.
The following results close the loop: Las Vegas compression search is not merely
blocked by one-way functions, it is *equivalent* to inverting them.  Randomness
is therefore worth exactly zero at the cryptographic boundary. -/







/-! ## Section 5: the calibration theorem -/


open scoped Classical



/-! ## Section 6: a strict hierarchy in the seed budget -/


open scoped Classical



/-! ## Section 7: the average-case constant is sharp -/


open scoped Classical

theorem CompressionLasVegas.avg_description_length_sharp(m : ℕ) :
    (∑ y ∈ bitStringsUpTo m, K (id : Str → Str) y) + 2 * 2 ^ (m + 1)
      = (m + 1) * 2 ^ (m + 1) + 2 ∧ (bitStringsUpTo m).card + 1 = 2 ^ (m + 1) := by sorry
