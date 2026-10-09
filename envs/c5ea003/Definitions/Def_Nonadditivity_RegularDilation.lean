-- Prove2me | Definitions.Def_Nonadditivity_RegularDilation
-- name    : Nonadditivity_RegularDilation
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:38:31.790681+00:00
-- url     : https://prove2.me/theorems/c202281e-da69-486a-966c-9b4e5d5705e7
-- title:
--   Coordinate operations for doubled regular polynomials
-- statement:
--   A matrix-coefficient regular polynomial acts on a vector-valued square-summable function by a finite sum of matrix actions at inverse-shifted group coordinates. Splitting a doubled coefficient space into its left and right components decomposes its squared norm as the sum of the component squared norms. The corresponding slices and right-coordinate embedding are defined on the full Hilbert spaces, with coordinate identities and an isometric right embedding. These operations supply the data for regular block dilation.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularDilation.lean#L24-L176

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularRestriction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # Hermitian dilation of literal matrix-valued regular polynomials

The inverse-transpose coefficients implement the actual Hilbert adjoint.
Orthogonal coordinate slices then give the norm of the doubled polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.RegularDilation

open RegularCoefficientEnergy
open scoped BigOperators ENNReal Matrix Matrix.Norms.L2Operator

variable {G ι : Type*} [Group G] [DecidableEq G] [Fintype ι] [DecidableEq ι]

omit [DecidableEq G] in
theorem regularPolynomial_apply (S : Finset G) (a : G → Matrix ι ι ℂ)
    (f : Hilbert G ι) (h : G) :
    regularPolynomial S a f h = ∑ w ∈ S, coefficientOperator (a w) (f (w⁻¹ * h)) := by
  rw [MatrixRegularRestriction.matrixPolynomial_eq]
  rw [MatrixRegularRestriction.coefficientPolynomial_apply]
  exact Finset.sum_coe_sort S (fun w => coefficientOperator (a w) (f (w⁻¹ * h)))











def fiberLeft (x : CoefficientSpace (Sum ι ι)) : CoefficientSpace ι :=
  WithLp.toLp 2 (fun i => x (Sum.inl i))

def fiberRight (x : CoefficientSpace (Sum ι ι)) : CoefficientSpace ι :=
  WithLp.toLp 2 (fun i => x (Sum.inr i))

omit [DecidableEq ι] in
@[simp] theorem fiberLeft_apply (x : CoefficientSpace (Sum ι ι)) (i : ι) :
    fiberLeft x i = x (Sum.inl i) := rfl

omit [DecidableEq ι] in
@[simp] theorem fiberRight_apply (x : CoefficientSpace (Sum ι ι)) (i : ι) :
    fiberRight x i = x (Sum.inr i) := rfl

omit [DecidableEq ι] in
theorem fiber_energy (x : CoefficientSpace (Sum ι ι)) :
    ‖x‖ ^ 2 = ‖fiberLeft x‖ ^ 2 + ‖fiberRight x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, fiberLeft_apply, fiberRight_apply]
  exact Fintype.sum_sum_type (fun i => ‖x i‖ ^ 2)

def leftSlice (f : Hilbert G (Sum ι ι)) : Hilbert G ι :=
  ⟨fun g => fiberLeft (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => ?_)
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        f.property.summable (by norm_num))
    nlinarith [fiber_energy (f g), sq_nonneg ‖fiberRight (f g)‖]⟩

def rightSlice (f : Hilbert G (Sum ι ι)) : Hilbert G ι :=
  ⟨fun g => fiberRight (f g), by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun g => ?_)
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        f.property.summable (by norm_num))
    nlinarith [fiber_energy (f g), sq_nonneg ‖fiberLeft (f g)‖]⟩

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem leftSlice_apply (f : Hilbert G (Sum ι ι)) (g : G) (i : ι) :
    leftSlice f g i = f g (Sum.inl i) := rfl

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem rightSlice_apply (f : Hilbert G (Sum ι ι)) (g : G) (i : ι) :
    rightSlice f g i = f g (Sum.inr i) := rfl



def fiberEmbedRight (x : CoefficientSpace ι) : CoefficientSpace (Sum ι ι) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => x i))

omit [DecidableEq ι] in
@[simp] theorem fiberLeft_embedRight (x : CoefficientSpace ι) :
    fiberLeft (fiberEmbedRight x) = 0 := by ext i; rfl

omit [DecidableEq ι] in
@[simp] theorem fiberRight_embedRight (x : CoefficientSpace ι) :
    fiberRight (fiberEmbedRight x) = x := by ext i; rfl

omit [DecidableEq ι] in
theorem fiberEmbedRight_norm (x : CoefficientSpace ι) : ‖fiberEmbedRight x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [fiber_energy]
  simp

def embedRight (f : Hilbert G ι) : Hilbert G (Sum ι ι) :=
  ⟨fun g => fiberEmbedRight (f g), by
    apply memℓp_gen
    simp only [fiberEmbedRight_norm]
    exact f.property.summable (by norm_num)⟩

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem leftSlice_embedRight (f : Hilbert G ι) : leftSlice (embedRight f) = 0 := by
  ext g i
  rfl

omit [Group G] [DecidableEq G] [DecidableEq ι] in
@[simp] theorem rightSlice_embedRight (f : Hilbert G ι) : rightSlice (embedRight f) = f := by
  ext g i
  rfl



















end Nonadditivity.RegularDilation


