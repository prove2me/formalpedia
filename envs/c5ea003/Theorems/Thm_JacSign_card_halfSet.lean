-- Prove2me | Theorems.Thm_JacSign_card_halfSet
-- name    : JacSign.card_halfSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:36:36.057482+00:00
-- url     : https://prove2.me/theorems/1314c9c2-9580-4970-8d81-7a2a41dd883b
-- title:
--   The lower half of the residues has `(p-1)/2` elements.
-- statement:
--   The lower half of the residues has `(p-1)/2` elements.
--
--   ```lean
--   theorem JacSign.card_halfSet(hp : p ≠ 2) : 2 * ((halfSet p).card : ℤ) = (p : ℤ) - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedTwoAdic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedTwoAdic.lean#L25

-- Thm stub generated from Tropical/JacobiSignedTwoAdic.lean
import Mathlib
import Definitions.Def_Tropical_JacobiSignedWeilFloorCore

/-!
# The exact 2-adic valuation of the Jacobi-signed circle count

Every observed value of the statistic is `2` times an *odd* number
(`-2, -6, 10, -10, 6, -14, -18, 22, 26, 34, ...`).  This is not a coincidence: we prove

`p ≡ 1 (mod 4) → W p ≡ 2 (mod 4)`  (`JacSign.W_mod_four`),

i.e. `v₂(W p) = 1` exactly.  The argument is a parity count over the "lower half" of the
residues: `W p = 2 S` with `S` a sum of `(p-1)/2` values in `{0, ±1}`, exactly one of which
(the term `x = 1`) vanishes, so `S ≡ (p-1)/2 - 1 ≡ 1 (mod 2)`.

Combined with the Jacobsthal identity of `JacobiSignedTwoSquares.lean` this pins down the
classical normalisation of Fermat's two-square decomposition: `p = a² + b²` with
`a = W p / 2` **odd**.
-/

open Finset

open JacSign

variable (p : ℕ) [Fact p.Prime]

theorem JacSign.card_halfSet(hp : p ≠ 2) : 2 * ((halfSet p).card : ℤ) = (p : ℤ) - 1 := by sorry
