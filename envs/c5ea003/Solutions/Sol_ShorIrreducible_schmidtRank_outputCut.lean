-- Prove2me | solution 1 for ShorIrreducible.schmidtRank_outputCut
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:49:41.872514+00:00
-- url     : https://prove2.me/submissions/5916d446-0811-4172-8881-70f1e4bc002d

-- Sol generated from Novelty/ShorQFTOutputState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorCutRankSharp
import Definitions.Def_Novelty_ShorQFTOutput
import Definitions.Def_Novelty_ShorQFTOutputState
import Theorems.Thm_ShorIrreducible_outputCutMatrix_eq_diagonal_mul
import Theorems.Thm_ShorIrreducible_schmidtRank_combCut_sharp

/-! # The QFT *output* state is entangled too

A common intuition about Shor's algorithm is that the QFT output is "nearly a
single basis state", so that only the *input* of the QFT is hard to represent
classically.  This file refutes that intuition inside the model: the output of
the QFT on a comb of period `r` in a register of size `Q = r · m` is again a
comb — of period `m`, with unit-modulus phases — and therefore has exactly the
same kind of exponential Schmidt rank across a register cut.

* `outputCutMatrix_eq_diagonal_mul` : the output state across a cut is the input
  comb of period `m` conjugated by two *diagonal unitaries* (a row phase
  `ζ^{j b}` and a column phase `ζ^{j B c}`);
* `schmidtRank_outputCut` : hence its Schmidt rank is exactly
  `min C (m / gcd(m, B))`, the same formula as for the input with `r` replaced
  by `m = Q / r`;
* `two_le_schmidtRank_outputCut` : the output is *not* a product state across
  the cut whenever `m ∤ B` — in particular it is not a single basis state;
* `not_hasBondDim_outputCut` : the bond-dimension obstruction applies at the
  output endpoint of the QFT as well as at the input.

Combined with `norm_combDFT` (all `r` surviving amplitudes have equal modulus)
this settles the "both endpoints of the QFT are entangled" claim.
-/

open Finset Matrix

open ShorIrreducible

open IITTensorNetwork


variable {B C m j Q : ℕ} [NeZero m] {amp : ℝ}



lemma isUnit_det_diagonal_zeta {n : ℕ} (f : Fin n → ℕ) (Q : ℕ) :
    IsUnit (Matrix.diagonal (fun i : Fin n => zeta Q ^ (f i))).det := by
  rw [Matrix.det_diagonal]
  refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
  exact pow_ne_zero _ (Complex.exp_ne_zero _)






open ShorIrreducible in
theorem solution(hamp : amp ≠ 0) (hm : 0 < m) (hB : m ≤ B) :
    schmidtRank (outputCutMatrix B C m j Q amp) = min C (cutPeriod m B) := by
  rw [schmidtRank, outputCutMatrix_eq_diagonal_mul,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_det_diagonal_zeta _ _),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_diagonal_zeta _ _),
    ← schmidtRank, schmidtRank_combCut_sharp hamp hm hB]
