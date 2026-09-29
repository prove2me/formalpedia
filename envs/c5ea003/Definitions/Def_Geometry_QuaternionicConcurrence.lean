-- Prove2me | Definitions.Def_Geometry_QuaternionicConcurrence
-- name    : Geometry_QuaternionicConcurrence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:53.906975+00:00
-- url     : https://prove2.me/theorems/93751a27-6ac4-435e-a4f8-0cae0e4f490d
-- title:
--   Aether Catalog definitions — Geometry_QuaternionicConcurrence
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.QuaternionicConcurrence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/QuaternionicConcurrence.lean by skeleton subtraction
import Mathlib

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

namespace QuaternionicConcurrence

/-- A pure two-qubit coefficient vector, arranged as a `2 × 2` matrix. -/
structure State where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ

namespace State

/-- Squared Hilbert norm of a two-qubit coefficient vector. -/
def normSq (ψ : State) : ℝ :=
  Complex.normSq ψ.a + Complex.normSq ψ.b +
    Complex.normSq ψ.c + Complex.normSq ψ.d

/-- The determinant (the exterior-square, or Plücker, coordinate). -/
def determinant (ψ : State) : ℂ := ψ.a * ψ.d - ψ.b * ψ.c

/-- Canonically normalized real Hopf functional.  On normalized states this is
standard pure-state concurrence.  The zero vector is assigned value zero. -/
def hopfFunctional (ψ : State) : ℝ :=
  if ψ.normSq = 0 then 0 else 2 * ‖ψ.determinant‖ / ψ.normSq

/-- Hermitian inner product of the two coefficient rows. -/
def rowInner (ψ : State) : ℂ := conj ψ.a * ψ.c + conj ψ.b * ψ.d

/-- Squared norm of the first coefficient row. -/
def firstRowNormSq (ψ : State) : ℝ :=
  Complex.normSq ψ.a + Complex.normSq ψ.b

/-- Squared norm of the second coefficient row. -/
def secondRowNormSq (ψ : State) : ℝ :=
  Complex.normSq ψ.c + Complex.normSq ψ.d






end State
end QuaternionicConcurrence


