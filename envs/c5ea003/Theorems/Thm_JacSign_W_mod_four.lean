-- Prove2me | Theorems.Thm_JacSign_W_mod_four
-- name    : JacSign.W_mod_four
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:36:53.377917+00:00
-- url     : https://prove2.me/theorems/6f9e9b79-30a4-4540-9ba4-d348a948c9ab
-- title:
--   The exact 2-adic valuation.
-- statement:
--   **The exact 2-adic valuation.** For `p ≡ 1 (mod 4)` the statistic is twice an odd
--   number: `W p ≡ 2 (mod 4)`.
--
--   ```lean
--   theorem JacSign.W_mod_four(hp : p ≠ 2) (h1 : p % 4 = 1) : ∃ s : ℤ, W p = 2 * s ∧ ¬ (2 : ℤ) ∣ s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/JacobiSignedTwoAdic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/JacobiSignedTwoAdic.lean#L73

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

theorem JacSign.W_mod_four(hp : p ≠ 2) (h1 : p % 4 = 1) : ∃ s : ℤ, W p = 2 * s ∧ ¬ (2 : ℤ) ∣ s := by sorry
