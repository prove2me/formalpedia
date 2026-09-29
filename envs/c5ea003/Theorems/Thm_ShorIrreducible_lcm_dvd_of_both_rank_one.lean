-- Prove2me | Theorems.Thm_ShorIrreducible_lcm_dvd_of_both_rank_one
-- name    : ShorIrreducible.lcm_dvd_of_both_rank_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:13:39.765687+00:00
-- url     : https://prove2.me/theorems/46cd3860-9983-456b-8a89-d661eedbddef
-- title:
--   A cut compresses both endpoints only when it is aligned with `lcm(r,m)`.
-- statement:
--   **A cut compresses both endpoints only when it is aligned with `lcm(r,m)`.**
--   Together with `not_dvd_pow_two_of_odd` this shows that no power-of-two cut of an
--   odd-order comb can be cheap at both ends of the QFT.
--
--   ```lean
--   theorem ShorIrreducible.lcm_dvd_of_both_rank_one[NeZero r] [NeZero m] (hamp : amp ≠ 0) (hr : 0 < r)
--       (hm : 0 < m) (hC : 2 ≤ C) (hrB : r ≤ B) (hmB : m ≤ B)
--       (hin : schmidtRank (combCutMatrix B C r x0 amp) = 1)
--       (hout : schmidtRank (outputCutMatrix B C m j Q amp) = 1) :
--       Nat.lcm r m ∣ B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorCutComplementarity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorCutComplementarity.lean#L111

-- Thm stub generated from Novelty/ShorCutComplementarity.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorQFTOutputState

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

theorem ShorIrreducible.lcm_dvd_of_both_rank_one[NeZero r] [NeZero m] (hamp : amp ≠ 0) (hr : 0 < r)
    (hm : 0 < m) (hC : 2 ≤ C) (hrB : r ≤ B) (hmB : m ≤ B)
    (hin : schmidtRank (combCutMatrix B C r x0 amp) = 1)
    (hout : schmidtRank (outputCutMatrix B C m j Q amp) = 1) :
    Nat.lcm r m ∣ B := by sorry
