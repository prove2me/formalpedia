-- Prove2me | solution 1 for ConvexOptimization.prekopa_marginal_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T15:47:14.901772+00:00
-- url     : https://prove2.me/submissions/8b1f0ba0-e137-4d09-8373-6d36d64e12cf

import Mathlib
import Definitions.Def_LogConcaveOn
import Theorems.Thm_ConvexOptimization_prekopa_leindler

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hf_int : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun y : EuclideanSpace ℝ (Fin m) => f (x, y))) :
    ConvexOptimization.LogConcaveOn Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y : EuclideanSpace ℝ (Fin m), f (x, y)) := by
  refine ⟨?_, ?_⟩
  · intro x _hx
    exact integral_nonneg (fun y => hf_lc.1 (x, y) (Set.mem_univ _))
  · intro x _hx y _hy a b ha hb hab
    have ha_eq : a = 1 - b := by linarith
    subst a
    by_cases hb0 : b = 0
    · subst b
      simp
    by_cases hb1 : b = 1
    · subst b
      simp

    have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb_lt : b < 1 := lt_of_le_of_ne (sub_nonneg.mp ha) hb1
    let xmix : EuclideanSpace ℝ (Fin n) := (1 - b) • x + b • y

    have hx_nonneg : ∀ z : EuclideanSpace ℝ (Fin m), 0 ≤ f (x, z) :=
      fun z => hf_lc.1 (x, z) (Set.mem_univ _)
    have hy_nonneg : ∀ z : EuclideanSpace ℝ (Fin m), 0 ≤ f (y, z) :=
      fun z => hf_lc.1 (y, z) (Set.mem_univ _)
    have hmix_nonneg : ∀ z : EuclideanSpace ℝ (Fin m), 0 ≤ f (xmix, z) :=
      fun z => hf_lc.1 (xmix, z) (Set.mem_univ _)

    have hx_meas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)) :=
      hf_meas.comp (measurable_const.prodMk measurable_id)
    have hy_meas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => f (y, z)) :=
      hf_meas.comp (measurable_const.prodMk measurable_id)
    have hmix_meas : Measurable (fun z : EuclideanSpace ℝ (Fin m) => f (xmix, z)) :=
      hf_meas.comp (measurable_const.prodMk measurable_id)

    have hPL := ConvexOptimization.prekopa_leindler (n := m) b hb_pos hb_lt
      (fun z : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (f (x, z)))
      (fun z : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (f (y, z)))
      (fun z : EuclideanSpace ℝ (Fin m) => ENNReal.ofReal (f (xmix, z)))
      (ENNReal.measurable_ofReal.comp hx_meas)
      (ENNReal.measurable_ofReal.comp hy_meas)
      (ENNReal.measurable_ofReal.comp hmix_meas)
      (fun u v => by
        have hreal := hf_lc.2 (x, u) (Set.mem_univ _) (y, v) (Set.mem_univ _)
          (1 - b) b ha hb (by ring)
        have hof := ENNReal.ofReal_le_ofReal hreal
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hx_nonneg u) _),
          ← ENNReal.ofReal_rpow_of_nonneg (hx_nonneg u) ha,
          ← ENNReal.ofReal_rpow_of_nonneg (hy_nonneg v) hb] at hof
        simpa [xmix] using hof)

    rw [← ofReal_integral_eq_lintegral_ofReal (hf_int x)
          (Filter.Eventually.of_forall hx_nonneg),
        ← ofReal_integral_eq_lintegral_ofReal (hf_int y)
          (Filter.Eventually.of_forall hy_nonneg),
        ← ofReal_integral_eq_lintegral_ofReal (hf_int xmix)
          (Filter.Eventually.of_forall hmix_nonneg)] at hPL

    have hx_int_nonneg : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin m), f (x, z) :=
      integral_nonneg hx_nonneg
    have hy_int_nonneg : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin m), f (y, z) :=
      integral_nonneg hy_nonneg
    have hmix_int_nonneg : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin m), f (xmix, z) :=
      integral_nonneg hmix_nonneg

    apply (ENNReal.ofReal_le_ofReal_iff hmix_int_nonneg).1
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hx_int_nonneg _),
      ← ENNReal.ofReal_rpow_of_nonneg hx_int_nonneg ha,
      ← ENNReal.ofReal_rpow_of_nonneg hy_int_nonneg hb]
    exact hPL
