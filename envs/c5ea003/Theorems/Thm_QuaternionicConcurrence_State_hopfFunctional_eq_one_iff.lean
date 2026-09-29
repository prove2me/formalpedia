-- Prove2me | Theorems.Thm_QuaternionicConcurrence_State_hopfFunctional_eq_one_iff
-- name    : QuaternionicConcurrence.State.hopfFunctional_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:41:08.808947+00:00
-- url     : https://prove2.me/theorems/780f2443-8682-41d4-acc3-c46b12dece60
-- title:
--   Exact classification of sharp determinant maximizers.
-- statement:
--   Exact classification of sharp determinant maximizers.  This strengthens
--   the mere upper bound: a normalized state has functional value one exactly when
--   its two coefficient rows are Hermitian-orthogonal and both have squared norm
--   `1/2`.
--
--   ```lean
--   theorem QuaternionicConcurrence.State.hopfFunctional_eq_one_iff(ψ : State) (hnorm : ψ.normSq = 1) :
--       ψ.hopfFunctional = 1 ↔
--         ψ.rowInner = 0 ∧ ψ.firstRowNormSq = 1 / 2 ∧ ψ.secondRowNormSq = 1 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/QuaternionicConcurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/QuaternionicConcurrence.lean#L84

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

theorem QuaternionicConcurrence.State.hopfFunctional_eq_one_iff(ψ : State) (hnorm : ψ.normSq = 1) :
    ψ.hopfFunctional = 1 ↔
      ψ.rowInner = 0 ∧ ψ.firstRowNormSq = 1 / 2 ∧ ψ.secondRowNormSq = 1 / 2 := by sorry
