-- Prove2me | solution 1 for ConvexOptimization.log_barrier_affine_self_concordant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T01:33:06.62266+00:00
-- url     : https://prove2.me/submissions/41d07b75-dec0-4092-a3a9-16dd465d4023

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance
import Theorems.Thm_ConvexOptimization_self_concordant_add

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open Set

namespace ConvexOptimization

lemma negLog_iteratedDeriv_two (c : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => -Real.log x) c = c⁻¹ ^ 2 := by
  simp [iteratedDeriv_succ]

lemma negLog_iteratedDeriv_three {c : ℝ} (hc : c ≠ 0) :
    iteratedDeriv 3 (fun x : ℝ => -Real.log x) c = -2 * c⁻¹ ^ 3 := by
  have hd : deriv (fun i : ℝ => (i ^ 2)⁻¹) c = -2 / c ^ 3 := by
    convert (((hasDerivAt_id c).pow 2).inv (pow_ne_zero 2 hc)).deriv using 1 <;>
      simp <;> field_simp <;> ring
  simp [iteratedDeriv_succ]
  rw [hd]
  field_simp

lemma affine_iteratedDeriv_two (c d : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => c + t * d) 0 = 0 := by
  simp [iteratedDeriv_succ]

lemma affine_iteratedDeriv_three (c d : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => c + t * d) 0 = 0 := by
  simp [iteratedDeriv_succ]

lemma negLog_affine_deriv_two {c d : ℝ} (hc : 0 < c) :
    iteratedDeriv 2 (fun t : ℝ => -Real.log (c + t * d)) 0 = c⁻¹ ^ 2 * d ^ 2 := by
  let f : ℝ → ℝ := fun t => c + t * d
  let g : ℝ → ℝ := fun y => -Real.log y
  have hg : ContDiffAt ℝ 2 g (f 0) := by
    simpa [f, g] using (Real.contDiffAt_log.2 hc.ne').neg
  have hf : ContDiffAt ℝ 2 f 0 := by fun_prop
  rw [show (fun t : ℝ => -Real.log (c + t * d)) = g ∘ f by rfl]
  rw [iteratedDeriv_comp_two hg hf]
  rw [show iteratedDeriv 2 g (f 0) = c⁻¹ ^ 2 by
    simpa [f, g] using negLog_iteratedDeriv_two c]
  simp [f, g, affine_iteratedDeriv_two]

lemma negLog_affine_deriv_three {c d : ℝ} (hc : 0 < c) :
    iteratedDeriv 3 (fun t : ℝ => -Real.log (c + t * d)) 0 = -2 * c⁻¹ ^ 3 * d ^ 3 := by
  let f : ℝ → ℝ := fun t => c + t * d
  let g : ℝ → ℝ := fun y => -Real.log y
  have hg : ContDiffAt ℝ 3 g (f 0) := by
    simpa [f, g] using (Real.contDiffAt_log.2 hc.ne').neg
  have hf : ContDiffAt ℝ 3 f 0 := by fun_prop
  rw [show (fun t : ℝ => -Real.log (c + t * d)) = g ∘ f by rfl]
  rw [iteratedDeriv_comp_three hg hf]
  rw [show iteratedDeriv 3 g (f 0) = -2 * c⁻¹ ^ 3 by
    simpa [f, g] using negLog_iteratedDeriv_three hc.ne']
  simp [f, g, affine_iteratedDeriv_two, affine_iteratedDeriv_three]

lemma negLog_affine_sc_ineq {c d : ℝ} (hc : 0 < c) :
    |iteratedDeriv 3 (fun t : ℝ => -Real.log (c + t * d)) 0| ≤
      2 * (iteratedDeriv 2 (fun t : ℝ => -Real.log (c + t * d)) 0) ^ ((3 : ℝ) / 2) := by
  rw [negLog_affine_deriv_two hc, negLog_affine_deriv_three hc]
  have hz : c⁻¹ ^ 2 * d ^ 2 = (c⁻¹ * d) ^ 2 := by ring
  rw [hz, Real.rpow_div_two_eq_sqrt 3 (sq_nonneg _), Real.sqrt_sq_eq_abs]
  simp [abs_mul, abs_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm]

lemma single_affine_barrier_sc {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n)) (b : ℝ) :
    IsSelfConcordantOn {x | ⟪a, x⟫ < b} (fun x => -Real.log (b - ⟪a, x⟫)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨convex_halfSpace_lt (innerSL ℝ a).toLinearMap.isLinear b, ?_⟩
    intro x hx y hy u v hu hv huv
    have hpx : 0 < b - ⟪a, x⟫ := sub_pos.mpr hx
    have hpy : 0 < b - ⟪a, y⟫ := sub_pos.mpr hy
    have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hpx hpy hu hv huv
    have heq : b - ⟪a, u • x + v • y⟫ =
        u • (b - ⟪a, x⟫) + v • (b - ⟪a, y⟫) := by
      simp only [inner_add_right, real_inner_smul_right]
      change b - (u * ⟪a, x⟫ + v * ⟪a, y⟫) =
        u * (b - ⟪a, x⟫) + v * (b - ⟪a, y⟫)
      calc
        b - (u * ⟪a, x⟫ + v * ⟪a, y⟫) =
            (u + v) * b - (u * ⟪a, x⟫ + v * ⟪a, y⟫) := by rw [huv]; ring
        _ = u * (b - ⟪a, x⟫) + v * (b - ⟪a, y⟫) := by ring
    change -Real.log (b - ⟪a, u • x + v • y⟫) ≤
      u * -Real.log (b - ⟪a, x⟫) + v * -Real.log (b - ⟪a, y⟫)
    rw [heq]
    change u * Real.log (b - ⟪a, x⟫) + v * Real.log (b - ⟪a, y⟫) ≤
      Real.log (u * (b - ⟪a, x⟫) + v * (b - ⟪a, y⟫)) at hlog
    calc
      -Real.log (u * (b - ⟪a, x⟫) + v * (b - ⟪a, y⟫)) ≤
          -(u * Real.log (b - ⟪a, x⟫) + v * Real.log (b - ⟪a, y⟫)) := neg_le_neg hlog
      _ = u * -Real.log (b - ⟪a, x⟫) + v * -Real.log (b - ⟪a, y⟫) := by ring
  · intro x hx
    have hn : b - ⟪a, x⟫ ≠ 0 := (sub_pos.mpr hx).ne'
    exact ((contDiffAt_const.sub (innerSL ℝ a).contDiff.contDiffAt).log hn).neg.contDiffWithinAt
  · intro x hx v
    have hc : 0 < b - ⟪a, x⟫ := sub_pos.mpr hx
    convert (negLog_affine_sc_ineq (c := b - ⟪a, x⟫) (d := -⟪a, v⟫) hc) using 1 <;>
      congr 3 <;> funext t <;>
      simp only [inner_add_right, real_inner_smul_right, smul_eq_mul] <;> ring


lemma IsSelfConcordantOn.mono {n : ℕ} {U Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : IsSelfConcordantOn U f)
    (hΩc : Convex ℝ Ω) (hsub : Ω ⊆ U) : IsSelfConcordantOn Ω f := by
  refine ⟨⟨hΩc, ?_⟩, hf.2.1.mono hsub, fun x hx => hf.2.2 x (hsub hx)⟩
  intro x hx y hy u v hu hv huv
  exact hf.1.2 (hsub hx) (hsub hy) hu hv huv

lemma zero_self_concordant {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩc : Convex ℝ Ω) : IsSelfConcordantOn Ω (fun _ => 0) := by
  refine ⟨convexOn_const 0 hΩc, contDiffOn_const, ?_⟩
  intro x hx v
  norm_num [iteratedDeriv_succ]

lemma affine_barrier_finset_sc {n m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (s : Finset (Fin m)) :
    IsSelfConcordantOn {x | ∀ i, ⟪a i, x⟫ < b i}
      (fun x => ∑ i ∈ s, -Real.log (b i - ⟪a i, x⟫)) := by
  let Ω : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, ⟪a i, x⟫ < b i}
  have hΩeq : Ω = ⋂ i, {x | ⟪a i, x⟫ < b i} := by ext x; simp [Ω]
  have hΩc : Convex ℝ Ω := by
    rw [hΩeq]
    exact convex_iInter fun i =>
      convex_halfSpace_lt (innerSL ℝ (a i)).toLinearMap.isLinear (b i)
  have hΩo : IsOpen Ω := by
    rw [hΩeq]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt (innerSL ℝ (a i)).continuous continuous_const
  induction s using Finset.induction_on with
  | empty => simpa [Ω] using zero_self_concordant Ω hΩc
  | @insert i s hi ih =>
      have hsingle : IsSelfConcordantOn Ω (fun x => -Real.log (b i - ⟪a i, x⟫)) :=
        (single_affine_barrier_sc (a i) (b i)).mono hΩc (fun x hx => hx i)
      have hadd := self_concordant_add Ω hΩo
        (fun x => -Real.log (b i - ⟪a i, x⟫))
        (fun x => ∑ j ∈ s, -Real.log (b j - ⟪a j, x⟫)) hsingle ih
      simpa only [Finset.sum_insert hi, Pi.add_apply] using hadd

end ConvexOptimization

theorem solution {n mI : ℕ}
    (a : Fin mI → EuclideanSpace ℝ (Fin n)) (b : Fin mI → ℝ) :
    ConvexOptimization.IsSelfConcordantOn {x | ∀ i, ⟪a i, x⟫ < b i}
      (fun x => -∑ i, Real.log (b i - ⟪a i, x⟫)) := by
  simpa only [Finset.sum_neg_distrib] using
    ConvexOptimization.affine_barrier_finset_sc a b Finset.univ
