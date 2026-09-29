-- Prove2me | Definitions.Def_Novelty_ShorQFTOutputState
-- name    : Novelty_ShorQFTOutputState
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:59:48.33187+00:00
-- url     : https://prove2.me/theorems/41d5bb35-3123-4f9d-8838-3dbe9621fac2
-- title:
--   Aether Catalog definitions — Novelty_ShorQFTOutputState
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ShorQFTOutputState`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ShorQFTOutputState.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ShorCutRankSharp
import Definitions.Def_Novelty_ShorQFTOutput

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

namespace ShorIrreducible

open IITTensorNetwork

section OutputState

variable {B C m j Q : ℕ} [NeZero m] {amp : ℝ}

/-- The QFT output state of a comb of period `r` in a register of size
`Q = r · m`, presented across the cut `x = b + B · c`.  Its support is the set
of multiples of `m`, and its amplitudes are `amp` times a phase. -/
noncomputable def outputCutMatrix (B C m j Q : ℕ) (amp : ℝ) : Matrix (Fin B) (Fin C) ℂ :=
  fun b c =>
    if m ∣ ((b : ℕ) + B * (c : ℕ)) then (amp : ℂ) * zeta Q ^ (j * ((b : ℕ) + B * (c : ℕ)))
    else 0






end OutputState

end ShorIrreducible


