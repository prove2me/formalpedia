-- Prove2me | Theorems.Thm_JacSign_neg_one_notMem_halfSet
-- name    : JacSign.neg_one_notMem_halfSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:02.572285+00:00
-- url     : https://prove2.me/theorems/6eb57256-473b-4fa3-aaa4-0b9e5dec769f
-- title:
--   Neg one notMem halfSet
-- statement:
--   Formal statement of `JacSign.neg_one_notMem_halfSet` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem JacSign.neg_one_notMem_halfSet(hp : p ≠ 2) : (-1 : ZMod p) ∉ halfSet p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedTwoAdic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedTwoAdic.lean#L57

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

theorem JacSign.neg_one_notMem_halfSet(hp : p ≠ 2) : (-1 : ZMod p) ∉ halfSet p := by sorry
