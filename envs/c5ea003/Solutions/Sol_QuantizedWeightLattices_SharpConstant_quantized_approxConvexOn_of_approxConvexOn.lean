-- Prove2me | solution 1 for QuantizedWeightLattices.SharpConstant.quantized_approxConvexOn_of_approxConvexOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:17:02.735019+00:00
-- url     : https://prove2.me/submissions/c247ccfb-15a0-43ea-a636-36c16da8e231

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharpConstant
open QuantizedWeightLattices QuantizedWeightLattices.SharpConstant Set Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : NNReal} {f : E → ℝ}
    (hL : LipschitzWith L f) (Q : Quantizer E)
    {ε : ℝ} (h : ApproxConvexOn ε univ f) :
    ApproxConvexOn (ε + 2 * (L : ℝ) * Q.radius) univ (f ∘ Q.toFun) := by
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
  have hc := h (mem_univ x) (mem_univ y) ha hb hab
  simp only [Function.comp] at hc ⊢
  nlinarith
