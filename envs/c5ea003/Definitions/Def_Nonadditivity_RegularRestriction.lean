-- Prove2me | Definitions.Def_Nonadditivity_RegularRestriction
-- name    : Nonadditivity_RegularRestriction
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:35:59.234955+00:00
-- url     : https://prove2.me/theorems/e1e2543e-60ad-41ae-a4ea-a341de1bb100
-- title:
--   Subgroup restriction and zero extension for regular polynomials
-- statement:
--   For a subgroup $H$ of a group $G$, right-coset coordinates identify $G$ with the coset index set times $H$. Square summable functions can be sliced along those cosets, and functions on a subgroup or any injectively embedded index set can be extended by zero. The bundle proves the associated energy decomposition and norm comparisons for finite scalar regular polynomials, including equality under an injective group homomorphism.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/RegularRestriction.lean#L22-L261

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_FreeModel
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
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






noncomputable section

namespace Nonadditivity.RegularRestriction

open scoped BigOperators ENNReal

set_option maxHeartbeats 800000
open Nonadditivity.FreeModel

variable {G : Type*} [Group G]

abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

 theorem rightCoset_mk_mul (H : Subgroup G) (q : RightCosets H) (h : H) :
    Quotient.mk'' ((h : G) * q.out) = q := by
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp

/-- Right coset coordinates realize the subgroup regular action on every fiber. -/
def rightCosetEquiv (H : Subgroup G) : RightCosets H × H ≃ G :=
  Equiv.ofBijective (fun p => (p.2 : G) * p.1.out) (by
    constructor
    · intro p r heq
      dsimp only at heq
      have hq : p.1 = r.1 := by
        rw [← Nonadditivity.RegularRestriction.rightCoset_mk_mul H p.1 p.2, ← Nonadditivity.RegularRestriction.rightCoset_mk_mul H r.1 r.2, heq]
      apply Prod.ext hq
      apply Subtype.ext
      rw [hq] at heq
      exact mul_right_cancel heq
    · intro g
      let q : RightCosets H := Quotient.mk'' g
      have hm : g * q.out⁻¹ ∈ H := by
        apply QuotientGroup.rightRel_apply.mp
        exact Quotient.exact (Quotient.out_eq q)
      refine ⟨(q, ⟨g * q.out⁻¹, hm⟩), ?_⟩
      simp [mul_assoc])

@[simp] theorem rightCosetEquiv_apply (H : Subgroup G) (q : RightCosets H) (h : H) :
    rightCosetEquiv H (q, h) = (h : G) * q.out := rfl

theorem norm_sq {α : Type*} (f : Hilbert α) :
    ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f

/-- Restriction to one right coset, identified with the subgroup. -/
def cosetSlice (H : Subgroup G) (q : RightCosets H) (f : Hilbert G) : Hilbert H :=
  ⟨fun h => f (rightCosetEquiv H (q, h)), by
    apply memℓp_gen
    exact (f.property.summable (by norm_num)).comp_injective (by
      intro a b heq
      exact (Prod.mk.inj (rightCosetEquiv H |>.injective heq)).2)⟩

@[simp] theorem cosetSlice_apply (H : Subgroup G) (q : RightCosets H)
    (f : Hilbert G) (h : H) : cosetSlice H q f h = f ((h : G) * q.out) := rfl

/-- The square norm splits exactly as the sum of the square norms on right cosets. -/
theorem coset_energy (H : Subgroup G) (f : Hilbert G) :
    ‖f‖ ^ 2 = ∑' q : RightCosets H, ‖cosetSlice H q f‖ ^ 2 := by
  rw [norm_sq, ← (rightCosetEquiv H).tsum_eq (fun x => ‖f x‖ ^ 2)]
  have hs : Summable (fun p : RightCosets H × H => ‖f (rightCosetEquiv H p)‖ ^ 2) :=
    (rightCosetEquiv H).summable_iff (f := fun x => ‖f x‖ ^ 2) |>.mpr
      (by simpa using f.property.summable (by norm_num))
  rw [hs.tsum_prod]
  apply tsum_congr
  intro q
  exact (norm_sq (cosetSlice H q f)).symm

theorem summable_coset_energy (H : Subgroup G) (f : Hilbert G) :
    Summable (fun q : RightCosets H => ‖cosetSlice H q f‖ ^ 2) := by
  have hs : Summable (fun p : RightCosets H × H => ‖f (rightCosetEquiv H p)‖ ^ 2) :=
    (rightCosetEquiv H).summable_iff (f := fun x => ‖f x‖ ^ 2) |>.mpr
      (by simpa using f.property.summable (by norm_num))
  convert hs.prod using 1
  funext q
  exact norm_sq (cosetSlice H q f)

/-- A finite scalar polynomial in the concrete regular shifts. -/
def regularPolynomial {α : Type*} [Group α] {I : Type*} [Fintype I]
    (w : I → α) (a : I → ℂ) : Hilbert α →L[ℂ] Hilbert α :=
  ∑ i, a i • leftRegular (w i)

@[simp] theorem regularPolynomial_apply {α : Type*} [Group α] {I : Type*} [Fintype I]
    (w : I → α) (a : I → ℂ) (f : Hilbert α) (x : α) :
    regularPolynomial w a f x = ∑ i, a i * f ((w i)⁻¹ * x) := by
  simp only [regularPolynomial, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  rw [lp.coeFn_sum]
  simp [lp.coeFn_smul, Finset.sum_apply]

/-- The restricted operator acts identically on every right coset. -/
theorem cosetSlice_regularPolynomial (H : Subgroup G) {I : Type*} [Fintype I]
    (w : I → H) (a : I → ℂ) (q : RightCosets H) (f : Hilbert G) :
    cosetSlice H q (regularPolynomial (fun i => (w i : G)) a f) =
      regularPolynomial w a (cosetSlice H q f) := by
  ext h
  simp [mul_assoc]

/-- The ambient regular norm cannot exceed the subgroup regular norm. -/
theorem regularPolynomial_subgroup_norm_le (H : Subgroup G) {I : Type*} [Fintype I]
    (w : I → H) (a : I → ℂ) :
    ‖regularPolynomial (fun i => (w i : G)) a‖ ≤ ‖regularPolynomial w a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [coset_energy H, mul_pow, coset_energy H,
    ← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro q
    rw [cosetSlice_regularPolynomial]
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        ((regularPolynomial w a).le_opNorm (cosetSlice H q f))
  · exact summable_coset_energy H _
  · exact (summable_coset_energy H f).mul_left _

/-- Extension by zero through an injection is an actual square-summable function. -/
def extendZero {α β : Type*} (j : α → β) (hj : Function.Injective j)
    (f : Hilbert α) : Hilbert β :=
  ⟨Function.extend j f 0, by
    apply memℓp_gen
    have hs := (summable_extend_zero hj).mpr (f.property.summable (by norm_num))
    convert hs using 1
    funext y
    simpa [Function.comp_def] using
      Function.apply_extend (g := (⇑f)) (fun z : ℂ => ‖z‖ ^ (2 : ℝ≥0∞).toReal) j (0 : β → ℂ) y⟩

@[simp] theorem extendZero_apply_image {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : Hilbert α) (x : α) :
    extendZero j hj f (j x) = f x := hj.extend_apply _ _ _

theorem extendZero_apply_outside {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : Hilbert α) (x : β) (hx : x ∉ Set.range j) :
    extendZero j hj f x = 0 := Function.extend_apply' _ _ _ hx

/-- Extension by zero preserves the Hilbert norm exactly. -/
theorem extendZero_norm {α β : Type*} (j : α → β)
    (hj : Function.Injective j) (f : Hilbert α) : ‖extendZero j hj f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq, norm_sq]
  have heq : (fun y => ‖extendZero j hj f y‖ ^ 2) =
      Function.extend j (fun x => ‖f x‖ ^ 2) 0 := by
    funext y
    simpa [extendZero, Function.comp_def] using
      Function.apply_extend (g := (⇑f)) (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) j (0 : β → ℂ) y
  rw [heq, tsum_extend_zero hj]







/-- Extension by zero intertwines a finite polynomial along any group embedding. -/
theorem extendZero_regularPolynomial {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {I : Type*} [Fintype I]
    (w : I → H) (a : I → ℂ) (f : Hilbert H) :
    regularPolynomial (fun i => φ (w i)) a (extendZero φ hφ f) =
      extendZero φ hφ (regularPolynomial w a f) := by
  classical
  ext g
  by_cases hg : g ∈ Set.range φ
  · obtain ⟨h, rfl⟩ := hg
    rw [extendZero_apply_image]
    simp only [regularPolynomial_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← map_inv, ← map_mul, extendZero_apply_image]
  · rw [extendZero_apply_outside _ _ _ _ hg, regularPolynomial_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hm : (φ (w i))⁻¹ * g ∉ Set.range φ := by
      rintro ⟨h, hh⟩
      apply hg
      refine ⟨w i * h, ?_⟩
      rw [map_mul, hh]
      simp
    rw [extendZero_apply_outside _ _ _ _ hm, mul_zero]

/-- The regular polynomial on an embedded group has at least the original norm. -/
theorem regularPolynomial_norm_le_of_injective {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {I : Type*} [Fintype I] (w : I → H) (a : I → ℂ) :
    ‖regularPolynomial w a‖ ≤ ‖regularPolynomial (fun i => φ (w i)) a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  have hb := (regularPolynomial (fun i => φ (w i)) a).le_opNorm (extendZero φ hφ f)
  rw [extendZero_regularPolynomial, extendZero_norm, extendZero_norm] at hb
  exact hb

/-- An injective group homomorphism preserves every finite regular polynomial norm.
The proof uses actual square-summable right coset fibers and extension by zero. -/
theorem regularPolynomial_injective_norm_eq {H : Type*} [Group H] (φ : H →* G)
    (hφ : Function.Injective φ) {I : Type*} [Fintype I] (w : I → H) (a : I → ℂ) :
    ‖regularPolynomial (fun i => φ (w i)) a‖ = ‖regularPolynomial w a‖ := by
  let e : H ≃* φ.range := MonoidHom.ofInjective hφ
  apply le_antisymm
  · calc
      ‖regularPolynomial (fun i => φ (w i)) a‖ =
          ‖regularPolynomial (fun i => (e (w i) : G)) a‖ := rfl
      _ ≤ ‖regularPolynomial (fun i => e (w i)) a‖ :=
        regularPolynomial_subgroup_norm_le φ.range _ a
      _ ≤ ‖regularPolynomial w a‖ := by
        simpa using regularPolynomial_norm_le_of_injective e.symm.toMonoidHom
          e.symm.injective (fun i => e (w i)) a
  · exact regularPolynomial_norm_le_of_injective φ hφ w a

/-- Group isomorphisms preserve the norm of the actual regular polynomial. -/
theorem regularPolynomial_equiv_norm_eq {H : Type*} [Group H] (e : H ≃* G)
    {I : Type*} [Fintype I] (w : I → H) (a : I → ℂ) :
    ‖regularPolynomial (fun i => e (w i)) a‖ = ‖regularPolynomial w a‖ :=
  regularPolynomial_injective_norm_eq e.toMonoidHom e.injective w a













end Nonadditivity.RegularRestriction


