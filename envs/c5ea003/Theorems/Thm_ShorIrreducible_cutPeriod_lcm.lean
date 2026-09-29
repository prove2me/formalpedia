-- Prove2me | Theorems.Thm_ShorIrreducible_cutPeriod_lcm
-- name    : ShorIrreducible.cutPeriod_lcm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:10:02.211439+00:00
-- url     : https://prove2.me/theorems/b63a8c46-d323-46b8-ad12-5d6d7ca3d2d8
-- title:
--   The joint cut period is the lcm of the endpoint cut periods.
-- statement:
--   **The joint cut period is the lcm of the endpoint cut periods.**
--
--   ```lean
--   theorem ShorIrreducible.cutPeriod_lcm(hr : 0 < r) (hm : 0 < m) :
--       cutPeriod (Nat.lcm r m) B = Nat.lcm (cutPeriod r B) (cutPeriod m B) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorCutComplementarity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorCutComplementarity.lean#L59

-- Thm stub generated from Novelty/ShorCutComplementarity.lean
import Mathlib
import Definitions.Def_Novelty_ShorCutRankSharp

/-! # The corrected input/output law for the two endpoints of the QFT

`ShorCutAlignment.not_complementary_ranks` refutes the naive complementarity
conjecture (`rank_in · rank_out` bounded below by a function of `min(r,m)`).
This file proves the corrected law suggested by that refutation.

The engine is an *order* characterisation of the cut period:
`r ∣ B · k ↔ (r / gcd(r,B)) ∣ k` (`dvd_mul_iff_cutPeriod_dvd`), i.e.
`cutPeriod r B` is the order of the block size `B` in `ℤ/r`.  From it:

* `cutPeriod_lcm` : `cutPeriod (lcm r m) B = lcm (cutPeriod r B) (cutPeriod m B)`
  — the joint cut period is the *lcm* of the two endpoint cut periods, not their
  product and not a complementary divisor pair;
* `schmidtRank_mul_ge` : `min C (cutPeriod (lcm r m) B) ≤ rank_in · rank_out`,
  the corrected complementarity inequality;
* `lcm_dvd_of_both_rank_one` : a cut compresses **both** endpoints only when the
  block size is a multiple of `lcm(r, m)` — so, by `not_dvd_pow_two_of_odd`, never
  for a power-of-two cut of an odd order.
-/

open Finset

open ShorIrreducible

open IITTensorNetwork


variable {B C r m x0 j Q : ℕ} {amp : ℝ}

theorem ShorIrreducible.cutPeriod_lcm(hr : 0 < r) (hm : 0 < m) :
    cutPeriod (Nat.lcm r m) B = Nat.lcm (cutPeriod r B) (cutPeriod m B) := by sorry
