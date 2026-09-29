-- Prove2me | solution 1 for ShorIrreducible.schmidtRank_combCut_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:51:30.080592+00:00
-- url     : https://prove2.me/submissions/9dc1cd93-f5dc-47cd-8712-9d0dd15021a4

-- Sol generated from Novelty/ShorCombState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_ShorIrreducible_combCutMatrix_eq_matchMatrix
import Theorems.Thm_ShorIrreducible_schmidtRank_matchMatrix

/-! # The periodic comb across a register cut: bond dimension is the order

After the function register of Shor's algorithm is measured, the exponent
register is left in the **periodic comb**

`c_x = [x ≡ x₀ (mod r)]`  (suitably normalized),  `x < Q = B * C`,

which is the *input of the quantum Fourier transform*.  A tensor-train / MPS
emulation cuts the exponent register into a low part `b < B` and a high part
`c < C` via `x = b + B·c`.  This file computes the Schmidt data of the comb
across such a cut.

Writing `combCutMatrix B C r x₀ amp` for the coefficient matrix of the comb
across the cut, the main results are:

* `combCutMatrix_eq_matchMatrix` : the comb across a cut is a fibre-matching
  state for the labels `b ↦ b mod r` and `c ↦ x₀ - B·c mod r`;
* `schmidtRank_combCut_le` : the Schmidt rank is at most `min r (min B C)` —
  the cut can never see more than the order;
* `schmidtRank_combCut_eq` : if `gcd(B, r) = 1` (automatic for a power-of-two
  cut of an *odd* order) and `r ≤ B`, `r ≤ C`, then the Schmidt rank is
  **exactly `r`**, and hence `bondDim_combCut_ge` : every MPS representation of
  the comb across that cut has bond dimension at least `r`;
* `flatSchmidtSpectrum_combCut` : in the opposite regime `B ≤ r`, `C ≤ r` the
  Schmidt spectrum is *flat* — all singular values are equal, so there is no
  tail to truncate;
* `schmidtRank_combCut_eq_one_of_dvd` : the *only* way the comb factorizes
  across the cut is `r ∣ B`, i.e. when the low half of the register already
  resolves the period.  This is the sharp form of the folklore
  `D = Θ(min(r, Q/r))`.
-/

open Finset Matrix
open scoped ComplexOrder

open ShorIrreducible

open IITTensorNetwork


variable {B C r x0 : ℕ} [NeZero r] {amp : ℝ}





/-! ### The generic upper bound -/

theorem card_matchSet_comb_le_order :
    (matchSet (combLeft B r) (combRight B C r x0)).card ≤ r := by
  classical
  calc (matchSet (combLeft B r) (combRight B C r x0)).card
      ≤ (univ : Finset (ZMod r)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = r := by rw [Finset.card_univ, ZMod.card]


/-! ### The exponential regime: rank exactly `r` -/






/-! ### The flat regime: no singular-value tail to truncate -/





/-! ### The degenerate regime -/




open ShorIrreducible in
theorem solution(hamp : amp ≠ 0) :
    schmidtRank (combCutMatrix B C r x0 amp) ≤ min r (min B C) := by
  classical
  rw [combCutMatrix_eq_matchMatrix, schmidtRank_matchMatrix hamp]
  refine le_min card_matchSet_comb_le_order (le_min ?_ ?_)
  · calc (matchSet (combLeft B r) (combRight B C r x0)).card
        ≤ ((univ : Finset (Fin B)).image (combLeft B r)).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ ≤ (univ : Finset (Fin B)).card := Finset.card_image_le
      _ = B := by simp
  · calc (matchSet (combLeft B r) (combRight B C r x0)).card
        ≤ ((univ : Finset (Fin C)).image (combRight B C r x0)).card :=
          Finset.card_le_card Finset.inter_subset_right
      _ ≤ (univ : Finset (Fin C)).card := Finset.card_image_le
      _ = C := by simp
