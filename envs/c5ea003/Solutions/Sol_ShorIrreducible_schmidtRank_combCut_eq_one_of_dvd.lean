-- Prove2me | solution 1 for ShorIrreducible.schmidtRank_combCut_eq_one_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:51:29.399832+00:00
-- url     : https://prove2.me/submissions/950bbc4c-e6fb-415f-b714-b960664d64af

-- Sol generated from Novelty/ShorCombState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank
import Theorems.Thm_ShorIrreducible_combCutMatrix_eq_matchMatrix
import Theorems.Thm_ShorIrreducible_image_combLeft_eq_univ
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



/-! ### The exponential regime: rank exactly `r` -/






/-! ### The flat regime: no singular-value tail to truncate -/





/-! ### The degenerate regime -/




open ShorIrreducible in
theorem solution(hamp : amp ≠ 0) (hdvd : r ∣ B) (hC : 0 < C)
    (hB : r ≤ B) :
    schmidtRank (combCutMatrix B C r x0 amp) = 1 := by
  classical
  have hB0 : (B : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff B r).mpr hdvd
  have hright : ∀ c : Fin C, combRight B C r x0 c = (x0 : ZMod r) := by
    intro c
    rw [combRight, hB0, zero_mul, sub_zero]
  have himg : (univ : Finset (Fin C)).image (combRight B C r x0) = {(x0 : ZMod r)} := by
    apply Finset.Subset.antisymm
    · intro s hs
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hs
      rw [hright c]
      exact Finset.mem_singleton_self _
    · intro s hs
      rw [Finset.mem_singleton] at hs
      subst hs
      exact Finset.mem_image.mpr ⟨⟨0, hC⟩, Finset.mem_univ _, hright _⟩
  rw [combCutMatrix_eq_matchMatrix, schmidtRank_matchMatrix hamp, matchSet,
    image_combLeft_eq_univ hB, himg, Finset.univ_inter, Finset.card_singleton]
