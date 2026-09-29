-- Prove2me | solution 1 for ShorIrreducible.two_le_schmidtRank_outputCut
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:54:09.910655+00:00
-- url     : https://prove2.me/submissions/db033448-e236-4996-8a56-40d9b4a19aed

-- Sol generated from Novelty/ShorQFTOutputState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorCutRankSharp
import Definitions.Def_Novelty_ShorQFTOutput
import Definitions.Def_Novelty_ShorQFTOutputState
import Theorems.Thm_ShorIrreducible_cutPeriod_pos
import Theorems.Thm_ShorIrreducible_schmidtRank_outputCut

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
theorem solution(hamp : amp ≠ 0) (hm : 0 < m) (hB : m ≤ B)
    (hC : 2 ≤ C) (hndvd : ¬ m ∣ B) :
    2 ≤ schmidtRank (outputCutMatrix B C m j Q amp) := by
  rw [schmidtRank_outputCut hamp hm hB]
  refine le_min hC ?_
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < cutPeriod m B := cutPeriod_pos hm
  have hone : cutPeriod m B = 1 := by omega
  have hgcd : Nat.gcd m B = m := by
    have hdvd : Nat.gcd m B ∣ m := Nat.gcd_dvd_left m B
    have hmul : Nat.gcd m B * (m / Nat.gcd m B) = m := Nat.mul_div_cancel' hdvd
    rw [cutPeriod] at hone
    rw [hone, mul_one] at hmul
    exact hmul
  exact hndvd (hgcd ▸ Nat.gcd_dvd_right m B)
