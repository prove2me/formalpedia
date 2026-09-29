-- Prove2me | Theorems.Thm_ShorIrreducible_combCutMatrix_eq_matchMatrix
-- name    : ShorIrreducible.combCutMatrix_eq_matchMatrix
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:10:42.484073+00:00
-- url     : https://prove2.me/theorems/295912d3-30d2-434b-a8b8-104b1802ba36
-- title:
--   The comb across a cut is a fibre-matching state.
-- statement:
--   The comb across a cut is a fibre-matching state.
--
--   ```lean
--   theorem ShorIrreducible.combCutMatrix_eq_matchMatrix(B C r x0 : ℕ) [NeZero r] (amp : ℝ) :
--       combCutMatrix B C r x0 amp = matchMatrix (combLeft B r) (combRight B C r x0) amp := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorCombState.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorCombState.lean#L56

-- Thm stub generated from Novelty/ShorCombState.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState
import Definitions.Def_Novelty_ShorFullState
import Definitions.Def_Novelty_ShorMatchRank

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

theorem ShorIrreducible.combCutMatrix_eq_matchMatrix(B C r x0 : ℕ) [NeZero r] (amp : ℝ) :
    combCutMatrix B C r x0 amp = matchMatrix (combLeft B r) (combRight B C r x0) amp := by sorry
