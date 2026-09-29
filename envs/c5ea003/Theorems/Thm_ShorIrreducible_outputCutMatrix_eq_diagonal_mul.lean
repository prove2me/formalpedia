-- Prove2me | Theorems.Thm_ShorIrreducible_outputCutMatrix_eq_diagonal_mul
-- name    : ShorIrreducible.outputCutMatrix_eq_diagonal_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:14:12.39795+00:00
-- url     : https://prove2.me/theorems/3a375b13-58bf-4434-8d32-a1bfe99cf8f4
-- title:
--   **The QFT output across a cut is the period-`m` comb conjugated by diagonal
-- statement:
--   **The QFT output across a cut is the period-`m` comb conjugated by diagonal
--   phase matrices.**
--
--   ```lean
--   theorem ShorIrreducible.outputCutMatrix_eq_diagonal_mul(B C m j Q : ℕ) (amp : ℝ) :
--       outputCutMatrix B C m j Q amp
--         = Matrix.diagonal (fun b : Fin B => zeta Q ^ (j * (b : ℕ)))
--             * combCutMatrix B C m 0 amp
--             * Matrix.diagonal (fun c : Fin C => zeta Q ^ (j * (B * (c : ℕ)))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorQFTOutputState.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorQFTOutputState.lean#L45

-- Thm stub generated from Novelty/ShorQFTOutputState.lean
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

theorem ShorIrreducible.outputCutMatrix_eq_diagonal_mul(B C m j Q : ℕ) (amp : ℝ) :
    outputCutMatrix B C m j Q amp
      = Matrix.diagonal (fun b : Fin B => zeta Q ^ (j * (b : ℕ)))
          * combCutMatrix B C m 0 amp
          * Matrix.diagonal (fun c : Fin C => zeta Q ^ (j * (B * (c : ℕ)))) := by sorry
