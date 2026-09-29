-- Prove2me | Theorems.Thm_composite_iff
-- name    : composite_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:17.852928+00:00
-- url     : https://prove2.me/theorems/3617af39-8681-48cf-b21c-df050da057c3
-- title:
--   A number n ≥ 2 is composite iff it has a nontrivial divisor.
-- statement:
--   A number n ≥ 2 is composite iff it has a nontrivial divisor.
--
--   ```lean
--   theorem composite_iff(n : ℕ) (hn : 2 ≤ n) :
--       ¬ Nat.Prime n ↔ ∃ d : ℕ, 2 ≤ d ∧ d < n ∧ d ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Logic/ModelTheory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Logic/ModelTheory.lean#L50

-- Thm stub generated from Algebra/Logic/ModelTheory.lean
import Mathlib

/-! # CatalogBuild.Logic.ModelTheory

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 10
-/

theorem composite_iff(n : ℕ) (hn : 2 ≤ n) :
    ¬ Nat.Prime n ↔ ∃ d : ℕ, 2 ≤ d ∧ d < n ∧ d ∣ n := by sorry
