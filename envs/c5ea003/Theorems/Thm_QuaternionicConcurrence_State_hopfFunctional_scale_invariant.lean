-- Prove2me | Theorems.Thm_QuaternionicConcurrence_State_hopfFunctional_scale_invariant
-- name    : QuaternionicConcurrence.State.hopfFunctional_scale_invariant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:41:30.625275+00:00
-- url     : https://prove2.me/theorems/2b8930c9-7370-4c6d-bbf6-a8e88dc97866
-- title:
--   The functional is unchanged by multiplication of all amplitudes by a
-- statement:
--   The functional is unchanged by multiplication of all amplitudes by a
--   nonzero complex scalar, so it descends from the unit sphere to projective/Hopf
--   geometry.
--
--   ```lean
--   theorem QuaternionicConcurrence.State.hopfFunctional_scale_invariant(ψ : State) (z : ℂ) (hz : z ≠ 0) :
--       hopfFunctional ⟨z * ψ.a, z * ψ.b, z * ψ.c, z * ψ.d⟩ =
--         hopfFunctional ψ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/QuaternionicConcurrence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/QuaternionicConcurrence.lean#L61

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

theorem QuaternionicConcurrence.State.hopfFunctional_scale_invariant(ψ : State) (z : ℂ) (hz : z ≠ 0) :
    hopfFunctional ⟨z * ψ.a, z * ψ.b, z * ψ.c, z * ψ.d⟩ =
      hopfFunctional ψ := by sorry
