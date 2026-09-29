-- Prove2me | solution 1 for ShorIrreducible.image_combLeft_eq_univ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:45:46.606048+00:00
-- url     : https://prove2.me/submissions/8edf33d4-a68c-4de4-a990-ca7a6db9c993

-- Sol generated from Novelty/ShorCombState.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorFullState

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
theorem solution(hB : r ≤ B) :
    (univ : Finset (Fin B)).image (combLeft B r) = univ := by
  classical
  refine Finset.eq_univ_of_forall fun s => ?_
  refine Finset.mem_image.mpr ⟨⟨s.val, lt_of_lt_of_le (ZMod.val_lt s) hB⟩, Finset.mem_univ _, ?_⟩
  rw [combLeft]
  exact ZMod.natCast_zmod_val s
