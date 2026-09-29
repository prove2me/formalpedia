-- Prove2me | Theorems.Thm_QuaternionicConcurrence_State_hopfFunctional_eq_zero_iff
-- name    : QuaternionicConcurrence.State.hopfFunctional_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:41:20.450572+00:00
-- url     : https://prove2.me/theorems/afce55ee-bd15-406b-88e0-b977cc978d0c
-- title:
--   The zero locus is exactly the determinant-zero (rank-one/product) locus.
-- statement:
--   The zero locus is exactly the determinant-zero (rank-one/product) locus.
--
--   ```lean
--   theorem QuaternionicConcurrence.State.hopfFunctional_eq_zero_iff(ψ : State) :
--       ψ.hopfFunctional = 0 ↔ ψ.determinant = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/QuaternionicConcurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/QuaternionicConcurrence.lean#L180

-- Thm stub generated from Geometry/QuaternionicConcurrence.lean
import Mathlib
import Definitions.Def_Geometry_QuaternionicConcurrence

/-!
# Quaternionic Hopf concurrence and its sharp maximizers

A two-qubit vector is a pair of complex rows.  Its quaternionic Hopf
coordinate has a distinguished complex component, the determinant.  This file
uses its canonically normalized modulus as a real-valued functional and proves
a rigid equality classification: on the unit sphere it is one exactly when
the coefficient rows are orthogonal and have equal squared norm.
-/

open Complex ComplexConjugate

noncomputable section

open QuaternionicConcurrence


open State

theorem QuaternionicConcurrence.State.hopfFunctional_eq_zero_iff(ψ : State) :
    ψ.hopfFunctional = 0 ↔ ψ.determinant = 0 := by sorry
