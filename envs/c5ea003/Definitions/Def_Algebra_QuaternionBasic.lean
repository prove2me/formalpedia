-- Prove2me | Definitions.Def_Algebra_QuaternionBasic
-- name    : Algebra_QuaternionBasic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:53:59.023221+00:00
-- url     : https://prove2.me/theorems/4a9c9bd7-b088-4d30-947d-471ed2837760
-- title:
--   Aether Catalog definitions — Algebra_QuaternionBasic
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QuaternionBasic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QuaternionBasic.lean by skeleton subtraction
import Mathlib
/-
# Quaternion Algebra: Basic Definitions and Properties

This file defines a real quaternion structure from scratch and proves
fundamental algebraic properties including:
- Multiplication (Hamilton's rules)
- Conjugation is an involution and anti-homomorphism
- Norm squared is multiplicative
- Inverse formula for nonzero quaternions
- Unit quaternion characterization
-/

namespace QuatAlg

/-- Real quaternion: q = re + imI·i + imJ·j + imK·k -/
@[ext]
structure Quat where
  re : ℝ
  imI : ℝ
  imJ : ℝ
  imK : ℝ

namespace Quat

/-! ## Basic instances -/

instance : Zero Quat := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Quat := ⟨⟨1, 0, 0, 0⟩⟩
instance : Neg Quat := ⟨fun q => ⟨-q.re, -q.imI, -q.imJ, -q.imK⟩⟩
instance : Add Quat := ⟨fun q₁ q₂ => ⟨q₁.re + q₂.re, q₁.imI + q₂.imI, q₁.imJ + q₂.imJ, q₁.imK + q₂.imK⟩⟩
instance : Sub Quat := ⟨fun q₁ q₂ => ⟨q₁.re - q₂.re, q₁.imI - q₂.imI, q₁.imJ - q₂.imJ, q₁.imK - q₂.imK⟩⟩

/-- Hamilton multiplication -/
instance : Mul Quat := ⟨fun q₁ q₂ =>
  ⟨q₁.re * q₂.re - q₁.imI * q₂.imI - q₁.imJ * q₂.imJ - q₁.imK * q₂.imK,
   q₁.re * q₂.imI + q₁.imI * q₂.re + q₁.imJ * q₂.imK - q₁.imK * q₂.imJ,
   q₁.re * q₂.imJ - q₁.imI * q₂.imK + q₁.imJ * q₂.re + q₁.imK * q₂.imI,
   q₁.re * q₂.imK + q₁.imI * q₂.imJ - q₁.imJ * q₂.imI + q₁.imK * q₂.re⟩⟩

instance : SMul ℝ Quat := ⟨fun r q => ⟨r * q.re, r * q.imI, r * q.imJ, r * q.imK⟩⟩

/-! ## Simp lemmas for components -/


/-! ## Ring axioms -/


/-! ## Conjugation -/

/-- Quaternion conjugation: conj(a + bi + cj + dk) = a - bi - cj - dk -/
def conj (q : Quat) : Quat := ⟨q.re, -q.imI, -q.imJ, -q.imK⟩





/-! ## Norm squared -/

/-- Squared norm: ‖q‖² = re² + imI² + imJ² + imK² -/
def normSq (q : Quat) : ℝ := q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2










/-! ## Inverse -/

/-- Inverse of a quaternion: q⁻¹ = conj(q) / normSq(q) -/
noncomputable def inv (q : Quat) : Quat :=
  ⟨q.re / normSq q, -q.imI / normSq q, -q.imJ / normSq q, -q.imK / normSq q⟩



/-! ## Unit quaternions -/

/-- A unit quaternion has normSq = 1 -/
def IsUnit (q : Quat) : Prop := normSq q = 1







/-! ## Pure quaternions -/

/-- A pure (imaginary) quaternion has re = 0 -/
def IsPure (q : Quat) : Prop := q.re = 0

/-- The subtype of pure quaternions -/
def PureQuat := {q : Quat // IsPure q}






end Quat

end QuatAlg


