-- Prove2me | Definitions.Def_Shared_CyclicProjectiveOrbits_Basic
-- name    : Shared_CyclicProjectiveOrbits_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:24.618574+00:00
-- url     : https://prove2.me/theorems/155d42fd-5aa3-44de-9145-b7934e938b6c
-- title:
--   Aether Catalog definitions — Shared_CyclicProjectiveOrbits_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CyclicProjectiveOrbits.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CyclicProjectiveOrbits/Basic.lean by skeleton subtraction
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Cyclic orbits on an affine rational normal curve

This file formalizes the elementary Vandermonde core behind the paper's construction.
The affine rational normal curve is `t ↦ (1,t,…,t^(r-1))`.  We show that distinct
parameters give independent curve points, that a diagonal symmetric-power operator
moves a point by scaling its parameter, and consequently that a finite geometric-
progression orbit is MDS whenever its parameters are distinct.
-/

namespace CyclicProjectiveOrbits

open Matrix

/-- The affine chart of the degree `r-1` rational normal curve. -/
def rncPoint {k : Type*} [Monoid k] (r : ℕ) (t : k) : Fin r → k :=
  fun j => t ^ (j : ℕ)

/-
Distinct affine parameters give distinct points of a nonconstant rational normal curve.
-/

/-
The matrix whose rows are rational-normal-curve points is the Vandermonde matrix.
-/

/-
Distinct parameters make the rational-normal-curve evaluation matrix nonsingular.
-/

/-
Consequently, any linear relation among `r` curve points at distinct parameters is zero.
-/

/-- The diagonal operator induced by `diag(1,q)` on the `(r-1)`st symmetric power. -/
def symmetricPowerDiagonal {k : Type*} [CommSemiring k] (r : ℕ) (q : k) :
    (Fin r → k) →ₗ[k] (Fin r → k) where
  toFun v j := q ^ (j : ℕ) * v j
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' _ _ := by ext; simp [mul_comm, mul_assoc]

/-
The symmetric-power diagonal operator preserves the curve and scales its parameter.
-/

/-
Iterating the operator produces a geometric progression on the curve.
-/

/-- An orbit segment is MDS when every choice of `r` orbit columns is independent. -/
def IsMDSOrbitSegment {k : Type*} [Field k] {r n : ℕ}
    (A : (Fin r → k) →ₗ[k] (Fin r → k)) (z : Fin r → k) : Prop :=
  ∀ e : Fin r ↪ Fin n, LinearIndependent k (fun i => A^[((e i : Fin n) : ℕ)] z)

/-
A geometric-progression symmetric-power orbit is MDS provided every selected
parameter `q^i * t` is distinct.
-/

/-
A convenient criterion: nonzero `t` and powers of `q` distinct through length `n`
imply that the corresponding Krylov orbit segment is MDS.
-/

end CyclicProjectiveOrbits


