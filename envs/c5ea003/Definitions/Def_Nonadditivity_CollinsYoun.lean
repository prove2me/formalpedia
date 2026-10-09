-- Prove2me | Definitions.Def_Nonadditivity_CollinsYoun
-- name    : Nonadditivity_CollinsYoun
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:36:46.247244+00:00
-- url     : https://prove2.me/theorems/64df4858-daf2-4a71-9c17-d1c126ec11af
-- title:
--   Scalar coefficient lengths and creation operators
-- statement:
--   For a complex square matrix $A$ on a finite index set, the coefficient length is $\bigl(\sum_{i,j}|A_{ij}|^2\bigr)^{1/2}$, the unnormalized Hilbert–Schmidt norm. This bundle records its squared-norm identity and the finite Hilbert space estimates used to control sums of scalar multiples and orthogonal vectors in the regular-representation construction. It also defines the off-diagonal coefficient matrix and the two-letter scalar creation operators, with zero diagonal identities.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/CollinsYoun.lean#L28-L319

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeModel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # Operator estimates behind Collins--Youn

The results here discharge concrete pieces of the free length-two estimate.
No external Haagerup or Collins--Youn inequality is assumed in these lemmas.
-/

noncomputable section

namespace Nonadditivity.CollinsYoun

open Nonadditivity.FreeModel Nonadditivity.FreeCreation
open scoped BigOperators InnerProductSpace

attribute [local instance] Classical.propDecidable

section HilbertEstimates

variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sum_sq_of_inner_zero (f : I → E)
    (horth : ∀ i j, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i, f i‖ ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  classical
  have hinner : inner ℂ (∑ i, f i) (∑ i, f i) = ∑ i, inner ℂ (f i) (f i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    exact Finset.sum_eq_single i
      (fun j _ hji => horth i j hji.symm) (by simp)
  have hr := congrArg Complex.re hinner
  have hn : ∀ x : E, Complex.re (inner ℂ x x) = ‖x‖ ^ 2 := by
    intro x
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  simpa only [Complex.re_sum, hn] using hr

theorem norm_sum_smul_sq_le (a : I → ℂ) (f : I → E) :
    ‖∑ i, a i • f i‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖f i‖ ^ 2 := by
  have hnorm : ‖∑ i, a i • f i‖ ≤ ∑ i, ‖a i‖ * ‖f i‖ := by
    simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => a i • f i)
  have hsum : 0 ≤ ∑ i, ‖a i‖ * ‖f i‖ := Finset.sum_nonneg (by intros; positivity)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖a i‖) (fun i => ‖f i‖)
  nlinarith [norm_nonneg (∑ i, a i • f i)]

end HilbertEstimates

section ConeEstimates

variable {α I : Type*} [DecidableEq α] [Fintype I]









end ConeEstimates

section LengthTwo

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem creation_comp_flip_zero (s : Letter α) :
    (creation s).comp (creation (flip s)) = 0 := by
  rw [creation_domain]
  ext f x
  simp only [ContinuousLinearMap.comp_apply, leftRegular_apply, mask_apply,
    creation_apply, ContinuousLinearMap.zero_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hx : Cone (flip s) ((letter s)⁻¹ * x) <;> simp [hx]

def doubleCreation (i j : α) :
    Hilbert (FreeGroup α) →L[ℂ] Hilbert (FreeGroup α) :=
  (creation (i,false)).comp (creation (j,true))

omit [Fintype α] in
@[simp] theorem doubleCreation_self (i : α) : doubleCreation i i = 0 := by
  simpa [doubleCreation, FreeCreation.flip] using creation_comp_flip_zero (i,false)





def coefficientLength (A : Matrix α α ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

omit [DecidableEq α] in
theorem coefficientLength_sq (A : Matrix α α ℂ) :
    coefficientLength A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
  Real.sq_sqrt (by positivity)



omit [DecidableEq α] in
theorem coefficientLength_eq_hsLength (A : Matrix α α ℂ) :
    coefficientLength A = AdjointPurity.hsLength A := by
  unfold coefficientLength AdjointPurity.hsLength
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]

















def offDiagonal (A : Matrix α α ℂ) : Matrix α α ℂ :=
  fun i j => if i = j then 0 else A i j

omit [Fintype α] in
@[simp] theorem offDiagonal_diagonal (A : Matrix α α ℂ) (i : α) : offDiagonal A i i = 0 :=
  by simp [offDiagonal]







end LengthTwo

end Nonadditivity.CollinsYoun


