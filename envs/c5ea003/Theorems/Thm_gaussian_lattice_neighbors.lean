-- Prove2me | Theorems.Thm_gaussian_lattice_neighbors
-- name    : gaussian_lattice_neighbors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T15:02:46.497399+00:00
-- url     : https://prove2.me/theorems/096ddfaa-a28d-4952-a9fa-bfa9cc80b702
-- title:
--   The unit Gaussian integers: exactly 4 elements of norm 1 (kissing number = 4)
-- statement:
--   The unit Gaussian integers: exactly 4 elements of norm 1 (kissing number = 4)
--
--   ```lean
--   theorem gaussian_lattice_neighbors(a b : ℤ) :
--       a ^ 2 + b ^ 2 = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨
--                             (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/QuantumSystems/DecoderApplications.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/QuantumSystems/DecoderApplications.lean#L15

-- Thm stub generated from Logic/QuantumSystems/DecoderApplications.lean
import Mathlib

/-! # CatalogBuild.Logic.DecoderApplications

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 13
-/

theorem gaussian_lattice_neighbors(a b : ℤ) :
    a ^ 2 + b ^ 2 = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨
                          (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by sorry
