-- Prove2me | solution 1 for QuantizedWeightLattices.quantized_approxConvex
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:11:25.140134+00:00
-- url     : https://prove2.me/submissions/4a35b810-c10d-40be-83d7-ede2b33493e1

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
open QuantizedWeightLattices Set Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : NNReal} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    (Q : Quantizer E) : ApproxConvexOn (2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun) := by
  -- quantization moves `f` by at most `L · radius`
  have hlip : ∀ x, |f (Q.toFun x) - f x| ≤ (L : ℝ) * Q.radius := by
    intro x
    have h1 := hL.dist_le_mul (Q.toFun x) x
    rw [Real.dist_eq, dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (Q.error_le x) L.coe_nonneg)
  intro x _ y _ a b ha hb hab
  have hx := abs_le.1 (hlip x)
  have hy := abs_le.1 (hlip y)
  have hz := abs_le.1 (hlip (a • x + b • y))
  have hax := mul_le_mul_of_nonneg_left hx.1 ha
  have hax' := mul_le_mul_of_nonneg_left hx.2 ha
  have hby := mul_le_mul_of_nonneg_left hy.1 hb
  have hby' := mul_le_mul_of_nonneg_left hy.2 hb
  have hr : a * ((L : ℝ) * Q.radius) + b * ((L : ℝ) * Q.radius) = (L : ℝ) * Q.radius := by
    rw [← add_mul, hab, one_mul]
  have hc := hf.2 (mem_univ x) (mem_univ y) ha hb hab
  simp only [Function.comp, smul_eq_mul] at hc ⊢
  nlinarith
