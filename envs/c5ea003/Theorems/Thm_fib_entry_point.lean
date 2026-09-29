-- Prove2me | Theorems.Thm_fib_entry_point
-- name    : fib_entry_point
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:42.164445+00:00
-- url     : https://prove2.me/theorems/7a38aec2-00d5-46bd-9b1a-65bd7f536343
-- title:
--   Fib entry point
-- statement:
--   Formal statement of `fib_entry_point` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem fib_entry_point(p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
--       p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/OpenDirections.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/OpenDirections.lean#L107

-- Thm stub generated from Algebra/OpenDirections.lean
import Mathlib
import Definitions.Def_Algebra_OpenDirections

/-! # CatalogBuild.Speculative.OpenDirections

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 42
-/
















set_option maxHeartbeats 2000000 in

theorem fib_entry_point(p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by sorry
