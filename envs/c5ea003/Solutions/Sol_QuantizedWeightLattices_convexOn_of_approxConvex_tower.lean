-- Prove2me | solution 1 for QuantizedWeightLattices.convexOn_of_approxConvex_tower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:16:55.881143+00:00
-- url     : https://prove2.me/submissions/57d0e021-7747-4f82-ab3d-c3d9649d5b8d

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
open QuantizedWeightLattices Set Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : NNReal} {f : E → ℝ}
    (hL : LipschitzWith L f)
    (Q : ℕ → Quantizer E) (eps : ℕ → ℝ)
    (hr : Tendsto (fun m => (Q m).radius) atTop (𝓝 0))
    (heps : Tendsto eps atTop (𝓝 0))
    (hac : ∀ m, ApproxConvexOn (eps m) univ (f ∘ (Q m).toFun)) :
    ConvexOn ℝ univ f := by
  -- each quantizer transfers approximate convexity back to `f`, with defect `ε_m + 2 L r_m`
  have hstep : ∀ m (x y : E) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ a * f x + b * f y + (eps m + 2 * (L : ℝ) * (Q m).radius) := by
    intro m x y a b ha hb hab
    have hlip : ∀ z, |f ((Q m).toFun z) - f z| ≤ (L : ℝ) * (Q m).radius := by
      intro z
      have h1 := hL.dist_le_mul ((Q m).toFun z) z
      rw [Real.dist_eq, dist_eq_norm] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left ((Q m).error_le z) L.coe_nonneg)
    have hx := abs_le.1 (hlip x)
    have hy := abs_le.1 (hlip y)
    have hz := abs_le.1 (hlip (a • x + b • y))
    have hax := mul_le_mul_of_nonneg_left hx.2 ha
    have hby := mul_le_mul_of_nonneg_left hy.2 hb
    have hr' : a * ((L : ℝ) * (Q m).radius) + b * ((L : ℝ) * (Q m).radius)
        = (L : ℝ) * (Q m).radius := by
      rw [← add_mul, hab, one_mul]
    have hc := hac m (mem_univ x) (mem_univ y) ha hb hab
    simp only [Function.comp] at hc
    nlinarith
  -- let the mesh and the defect go to zero
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hlim : Tendsto (fun m => a * f x + b * f y + (eps m + 2 * (L : ℝ) * (Q m).radius)) atTop
      (𝓝 (a * f x + b * f y + (0 + 2 * (L : ℝ) * 0))) :=
    tendsto_const_nhds.add (heps.add (tendsto_const_nhds.mul hr))
  rw [mul_zero, add_zero, add_zero] at hlim
  simp only [smul_eq_mul]
  exact ge_of_tendsto' hlim (fun m => hstep m x y a b ha hb hab)
