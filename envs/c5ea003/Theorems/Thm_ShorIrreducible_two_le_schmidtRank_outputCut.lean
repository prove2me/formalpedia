-- Prove2me | Theorems.Thm_ShorIrreducible_two_le_schmidtRank_outputCut
-- name    : ShorIrreducible.two_le_schmidtRank_outputCut
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:14:46.017519+00:00
-- url     : https://prove2.me/theorems/c0b88917-cd10-41e1-9d97-0c533645d125
-- title:
--   The QFT output is not a product state across the cut — a fortiori not a
-- statement:
--   **The QFT output is not a product state across the cut** — a fortiori not a
--   single basis state — as soon as the block size does not resolve the output
--   period.
--
--   ```lean
--   theorem ShorIrreducible.two_le_schmidtRank_outputCut(hamp : amp ≠ 0) (hm : 0 < m) (hB : m ≤ B)
--       (hC : 2 ≤ C) (hndvd : ¬ m ∣ B) :
--       2 ≤ schmidtRank (outputCutMatrix B C m j Q amp) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorQFTOutputState.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorQFTOutputState.lean#L82

-- Thm stub generated from Novelty/ShorQFTOutputState.lean
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
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

theorem ShorIrreducible.two_le_schmidtRank_outputCut(hamp : amp ≠ 0) (hm : 0 < m) (hB : m ≤ B)
    (hC : 2 ≤ C) (hndvd : ¬ m ∣ B) :
    2 ≤ schmidtRank (outputCutMatrix B C m j Q amp) := by sorry
