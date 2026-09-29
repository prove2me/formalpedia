-- Prove2me | Definitions.Def_Novelty_ShorCombState
-- name    : Novelty_ShorCombState
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:58:05.683145+00:00
-- url     : https://prove2.me/theorems/ef1febf6-ef5c-437c-b4ed-51514e2cc1bc
-- title:
--   Aether Catalog definitions — Novelty_ShorCombState
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShorCombState`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShorCombState.lean by skeleton subtraction
import Mathlib
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

namespace ShorIrreducible

open IITTensorNetwork

section Comb

variable {B C r x0 : ℕ} [NeZero r] {amp : ℝ}

/-- Label of the low half of the exponent register: its residue mod `r`. -/
def combLeft (B r : ℕ) : Fin B → ZMod r := fun b => ((b : ℕ) : ZMod r)

/-- Label of the high half: the residue the low half has to complete to `x₀`. -/
def combRight (B C r x0 : ℕ) : Fin C → ZMod r :=
  fun c => (x0 : ZMod r) - (B : ZMod r) * ((c : ℕ) : ZMod r)

/-- The **periodic comb** `[x ≡ x₀ mod r]` across the cut `x = b + B·c`. -/
noncomputable def combCutMatrix (B C r x0 : ℕ) (amp : ℝ) : Matrix (Fin B) (Fin C) ℂ :=
  fun b c => if ((b : ℕ) + B * (c : ℕ)) % r = x0 % r then (amp : ℂ) else 0


/-! ### The generic upper bound -/



/-! ### The exponential regime: rank exactly `r` -/






/-! ### The flat regime: no singular-value tail to truncate -/





/-! ### The degenerate regime -/


end Comb

end ShorIrreducible


