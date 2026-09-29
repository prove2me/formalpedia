-- Prove2me | solution 1 for ShorIrreducible.outputCutMatrix_eq_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:47:41.413881+00:00
-- url     : https://prove2.me/submissions/4c3df067-c1ec-4834-be6b-5d5ce14ca145

-- Sol generated from Novelty/ShorQFTOutputState.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorCutRankSharp
import Definitions.Def_Novelty_ShorQFTOutput
import Definitions.Def_Novelty_ShorQFTOutputState

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









open ShorIrreducible in
theorem solution(B C m j Q : ℕ) (amp : ℝ) :
    outputCutMatrix B C m j Q amp
      = Matrix.diagonal (fun b : Fin B => zeta Q ^ (j * (b : ℕ)))
          * combCutMatrix B C m 0 amp
          * Matrix.diagonal (fun c : Fin C => zeta Q ^ (j * (B * (c : ℕ)))) := by
  ext b c
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : m ∣ ((b : ℕ) + B * (c : ℕ))
  · have hmod : ((b : ℕ) + B * (c : ℕ)) % m = 0 % m := by
      rw [Nat.zero_mod]
      exact Nat.dvd_iff_mod_eq_zero.mp h
    rw [outputCutMatrix, if_pos h, combCutMatrix, if_pos hmod,
      show j * ((b : ℕ) + B * (c : ℕ)) = j * (b : ℕ) + j * (B * (c : ℕ)) by ring, pow_add]
    ring
  · have hmod : ¬ ((b : ℕ) + B * (c : ℕ)) % m = 0 % m := by
      rw [Nat.zero_mod]
      exact fun hc => h (Nat.dvd_iff_mod_eq_zero.mpr hc)
    rw [outputCutMatrix, if_neg h, combCutMatrix, if_neg hmod]
    ring
