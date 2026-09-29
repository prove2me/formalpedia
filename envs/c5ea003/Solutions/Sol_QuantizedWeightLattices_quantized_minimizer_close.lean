-- Prove2me | solution 1 for QuantizedWeightLattices.quantized_minimizer_close
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:27:28.491985+00:00
-- url     : https://prove2.me/submissions/303185ba-5ad3-4d55-8de3-215403d68c9a

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
open QuantizedWeightLattices Set Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] {L : NNReal} {f : E → ℝ}
    {μ : ℝ} (hμ : 0 < μ) {x₀ ŵ : E}
    (hL : LipschitzWith L f) (Q : Quantizer E)
    (hgrowth : ∀ x, μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀)
    (hlat : ∀ x, f ŵ ≤ f (Q.toFun x)) :
    ‖ŵ - x₀‖ ≤ Real.sqrt (2 * (L : ℝ) * Q.radius / μ) := by
  -- quantization moves `f` by at most `L · radius`
  have hlip : ∀ x, |f (Q.toFun x) - f x| ≤ (L : ℝ) * Q.radius := by
    intro x
    have h1 := hL.dist_le_mul (Q.toFun x) x
    rw [Real.dist_eq, dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (Q.error_le x) L.coe_nonneg)
  -- growth at `ŵ` is paid for by the lattice point next to `x₀`
  have h1 := hgrowth ŵ
  have h2 := hlat x₀
  have h3 := (abs_le.1 (hlip x₀)).2
  rw [← Real.sqrt_sq (norm_nonneg (ŵ - x₀))]
  apply Real.sqrt_le_sqrt
  rw [le_div_iff₀ hμ]
  nlinarith
