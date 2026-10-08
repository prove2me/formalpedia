-- Prove2me | solution 1 for ConvexOptimization.prekopa_leindler_one_dimensional
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T02:48:12.290278+00:00
-- url     : https://prove2.me/submissions/2a4b031e-71e4-4e82-a2bc-16a7ef736828

import Mathlib
import Theorems.Thm_ConvexOptimization_prekopa_leindler_real_line

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace PrekopaLeindlerOneDimensionalAux

def PLAt (E : Type*) [MeasurableSpace E] [Add E] [SMul ℝ E]
    (μ : Measure E) (l : ℝ) : Prop :=
  ∀ (f g h : E → ℝ≥0∞), Measurable f → Measurable g → Measurable h →
    (∀ x y : E, f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - l) * (∫⁻ x, g x ∂μ) ^ l ≤ ∫⁻ x, h x ∂μ

theorem PLAt.linearEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [AddCommMonoid α] [AddCommMonoid β] [Module ℝ α] [Module ℝ β]
    (μ : Measure α) (ν : Measure β) {l : ℝ}
    (e : α ≃ₗ[ℝ] β) (he' : Measurable e.symm)
    (hmp : MeasurePreserving e μ ν) (hβ : PLAt β ν l) :
    PLAt α μ l := by
  intro f g h hf hg hh hple
  have hF : Measurable (fun b ↦ f (e.symm b)) := hf.comp he'
  have hG : Measurable (fun b ↦ g (e.symm b)) := hg.comp he'
  have hH : Measurable (fun b ↦ h (e.symm b)) := hh.comp he'
  have hres := hβ
    (fun b ↦ f (e.symm b))
    (fun b ↦ g (e.symm b))
    (fun b ↦ h (e.symm b))
    hF hG hH (by
      intro x y
      simpa using hple (e.symm x) (e.symm y))
  have int_f : (∫⁻ b, f (e.symm b) ∂ν) = ∫⁻ a, f a ∂μ := by
    calc
      _ = ∫⁻ a, f (e.symm (e a)) ∂μ := (hmp.lintegral_comp hF).symm
      _ = _ := by simp
  have int_g : (∫⁻ b, g (e.symm b) ∂ν) = ∫⁻ a, g a ∂μ := by
    calc
      _ = ∫⁻ a, g (e.symm (e a)) ∂μ := (hmp.lintegral_comp hG).symm
      _ = _ := by simp
  have int_h : (∫⁻ b, h (e.symm b) ∂ν) = ∫⁻ a, h a ∂μ := by
    calc
      _ = ∫⁻ a, h (e.symm (e a)) ∂μ := (hmp.lintegral_comp hH).symm
      _ = _ := by simp
  rwa [int_f, int_g, int_h] at hres

end PrekopaLeindlerOneDimensionalAux

open PrekopaLeindlerOneDimensionalAux

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : EuclideanSpace ℝ (Fin 1) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : EuclideanSpace ℝ (Fin 1),
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by
  have hR := ConvexOptimization.prekopa_leindler_real_line l hl0 hl1
  change PLAt ℝ volume l at hR

  have hRaw : PLAt (Fin 1 → ℝ) volume l := by
    apply PLAt.linearEquiv volume volume (LinearEquiv.funUnique (Fin 1) ℝ ℝ)
    · exact (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurable
    · exact volume_preserving_funUnique (Fin 1) ℝ
    · exact hR

  have hEuclidean : PLAt (EuclideanSpace ℝ (Fin 1)) volume l :=
    PLAt.linearEquiv volume volume
      (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ))
      (WithLp.measurable_toLp 2 (Fin 1 → ℝ))
      (PiLp.volume_preserving_ofLp (Fin 1)) hRaw

  exact hEuclidean f g h hf hg hh hple
