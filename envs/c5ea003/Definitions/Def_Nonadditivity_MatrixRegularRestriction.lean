-- Prove2me | Definitions.Def_Nonadditivity_MatrixRegularRestriction
-- name    : Nonadditivity_MatrixRegularRestriction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:37:03.188319+00:00
-- url     : https://prove2.me/theorems/f7c8b5aa-db26-4431-92a9-748888a48b00
-- title:
--   Regular polynomials with bounded operator coefficients
-- statement:
--   For a group $G$, a finite index set $I$, words $w_i\in G$, and bounded complex linear maps $A_i:E\to E$ on the coefficient Hilbert space, define $P=\sum_i\widetilde A_i\lambda_{w_i}$ on $\ell^2(G;E)$. Thus $(Pf)(x)=\sum_i A_i(f(w_i^{-1}x))$. The bundle supplies the corresponding vector-valued regular shifts, polynomial action, and squared-norm expression; the index set may be empty, yielding the zero polynomial. Right-coset slicing and extension by zero through an injection are constructed as actual vector-valued square summable functions, with their coordinate identities.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/MatrixRegularRestriction.lean#L29-L222

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Linearization
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




/-! # Matrix coefficient regular norms under group embeddings

Coset energy decomposition and extension by zero prove complete norm preservation:
the coefficient space can be any complex normed space and the coefficients any
bounded linear operators. The final theorem specializes to the literal finite
matrix coefficient polynomial from `RegularCoefficientEnergy`.
-/

noncomputable section

namespace Nonadditivity.MatrixRegularRestriction

open scoped BigOperators ENNReal
open Nonadditivity.RegularRestriction (RightCosets rightCosetEquiv)
open Nonadditivity.RegularCoefficientEnergy (VectorHilbert)

set_option maxHeartbeats 800000

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
theorem norm_sq {α : Type*} (f : VectorHilbert α E) :
    ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f

/-- Restriction to one right coset, identified with the subgroup. -/
def cosetSlice (H : Subgroup G) (q : RightCosets H) (f : VectorHilbert G E) : VectorHilbert H E :=
  ⟨fun h => f (rightCosetEquiv H (q, h)), by
    apply memℓp_gen
    exact (f.property.summable (by norm_num)).comp_injective (by
      intro a b heq
      exact (Prod.mk.inj (rightCosetEquiv H |>.injective heq)).2)⟩

omit [NormedSpace ℂ E] in
@[simp] theorem cosetSlice_apply (H : Subgroup G) (q : RightCosets H)
    (f : VectorHilbert G E) (h : H) : cosetSlice H q f h = f ((h : G) * q.out) := rfl





/-- The vector-valued regular shift. -/
def leftRegular {α : Type*} [Group α] (g : α) :
    VectorHilbert α E →L[ℂ] VectorHilbert α E :=
  (RegularCoefficientEnergy.reindexIsometry (E := E) (Equiv.mulLeft g⁻¹)).toLinearIsometry.toContinuousLinearMap

@[simp] theorem leftRegular_apply {α : Type*} [Group α] (g : α)
    (f : VectorHilbert α E) (h : α) : leftRegular g f h = f (g⁻¹ * h) := rfl

/-- A finite polynomial with arbitrary bounded operator coefficients. -/
def coefficientPolynomial {α : Type*} [Group α] {I : Type*} [Fintype I]
    (w : I → α) (a : I → E →L[ℂ] E) : VectorHilbert α E →L[ℂ] VectorHilbert α E :=
  ∑ i, (RegularCoefficientEnergy.liftOperator (a i)).comp (leftRegular (w i))

@[simp] theorem coefficientPolynomial_apply {α : Type*} [Group α] {I : Type*} [Fintype I]
    (w : I → α) (a : I → E →L[ℂ] E) (f : VectorHilbert α E) (x : α) :
    coefficientPolynomial w a f x = ∑ i, a i (f ((w i)⁻¹ * x)) := by
  simp only [coefficientPolynomial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply]





/-- Extension by zero through an injection is an actual square-summable function. -/
def extendZero {α β : Type*} (j : α → β) (hj : Function.Injective j)
    (f : VectorHilbert α E) : VectorHilbert β E :=
  ⟨Function.extend j f 0, by
    apply memℓp_gen
    have hs := (summable_extend_zero hj).mpr (f.property.summable (by norm_num))
    convert hs using 1
    funext y
    simpa [Function.comp_def] using
      Function.apply_extend (g := (⇑f)) (fun z : E => ‖z‖ ^ (2 : ℝ≥0∞).toReal) j (0 : β → E) y⟩

omit [NormedSpace ℂ E] in
@[simp] theorem extendZero_apply_image {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : VectorHilbert α E) (x : α) :
    extendZero j hj f (j x) = f x := hj.extend_apply _ _ _













section Matrix

variable [DecidableEq G] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq G] in
/-- The generic coefficient polynomial specializes to the literal matrix polynomial. -/
theorem matrixPolynomial_eq (S : Finset G) (c : G → Matrix ι ι ℂ) :
    RegularCoefficientEnergy.regularPolynomial S c =
      coefficientPolynomial (fun w : S => w.val)
        (fun w => RegularCoefficientEnergy.coefficientOperator (c w.val)) := by
  simp only [RegularCoefficientEnergy.regularPolynomial, coefficientPolynomial]
  rw [← Finset.sum_coe_sort S (fun w =>
    (RegularCoefficientEnergy.liftOperator (RegularCoefficientEnergy.coefficientOperator (c w))).comp
      (RegularCoefficientEnergy.leftRegular w))]
  rfl





end Matrix

end Nonadditivity.MatrixRegularRestriction


