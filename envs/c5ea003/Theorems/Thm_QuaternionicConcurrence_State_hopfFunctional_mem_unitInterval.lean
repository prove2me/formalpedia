-- Prove2me | Theorems.Thm_QuaternionicConcurrence_State_hopfFunctional_mem_unitInterval
-- name    : QuaternionicConcurrence.State.hopfFunctional_mem_unitInterval
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:41:11.577257+00:00
-- url     : https://prove2.me/theorems/3aa42fd8-d181-4037-8952-72ddf8370663
-- title:
--   On normalized states the canonical functional lies in the unit interval.
-- statement:
--   On normalized states the canonical functional lies in the unit interval.
--
--   ```lean
--   theorem QuaternionicConcurrence.State.hopfFunctional_mem_unitInterval(ψ : State) (hnorm : ψ.normSq = 1) :
--       0 ≤ ψ.hopfFunctional ∧ ψ.hopfFunctional ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/QuaternionicConcurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/QuaternionicConcurrence.lean#L146

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

theorem QuaternionicConcurrence.State.hopfFunctional_mem_unitInterval(ψ : State) (hnorm : ψ.normSq = 1) :
    0 ≤ ψ.hopfFunctional ∧ ψ.hopfFunctional ≤ 1 := by sorry
