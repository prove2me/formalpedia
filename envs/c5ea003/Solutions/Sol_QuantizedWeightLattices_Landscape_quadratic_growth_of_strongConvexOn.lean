-- Prove2me | solution 1 for QuantizedWeightLattices.Landscape.quadratic_growth_of_strongConvexOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:35:28.614705+00:00
-- url     : https://prove2.me/submissions/d083d4f5-d900-4ae2-a328-4c776f4e315b

-- Sol generated from Bridges/QuantizedWeightLatticesLandscape.lean
import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLatticesLandscape
import Definitions.Def_Bridges_QuantizedWeightLatticesSharp
/-
Copyright (c) 2026. Phase A Research Mission: Bridge NumberTheory ↔ Machine Learning.

# Arithmetic Geometry of Transformer Weight Lattices, IV: landscape invariants

Third cycle of the research loop.  Having established that grid quantization
perturbs convexity by at most `2·L·r` (file I), that the codebook is the torsion
of the weight torus (file II) and that the bound is sharp within a factor two
(file III), we now show that the *finer* invariants of the loss landscape also
survive quantization.

* `quadratic_growth_of_strongConvexOn` — strong convexity forces quadratic growth
  around a global minimiser (proved by an explicit limiting argument along
  `t = 1/(n+1)`).
* `strongConvex_quantized_minimizer_close` — consequently, for a strongly convex
  loss *every* lattice-optimal weight lies within `√(2Lr/μ)` of the true optimum.
* `quantized_approxStrongConvex` — the whole strong-convexity modulus `μ` is
  transported to the quantized landscape, with the same additive defect `2Lr`;
  in particular the curvature invariant `μ` itself is preserved exactly.
* `lattice_infimum_close` — the optimal value of the lattice-restricted problem
  and of the continuous problem differ by at most `L·r`.
-/


open QuantizedWeightLattices.Landscape

open QuantizedWeightLattices Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Section 1: strong convexity gives quadratic growth at the optimum -/



/-! ## Section 2: the curvature modulus survives quantization -/



/-! ## Section 3: the optimal value is preserved -/



open QuantizedWeightLattices.Landscape in
theorem solution{μ : ℝ} {f : E → ℝ} {x₀ : E}
    (hf : StrongConvexOn univ μ f) (hmin : ∀ x, f x₀ ≤ f x) (x : E) :
    μ / 2 * ‖x - x₀‖ ^ 2 ≤ f x - f x₀ := by
  set C : ℝ := μ / 2 * ‖x - x₀‖ ^ 2 with hC
  have key : ∀ n : ℕ, (1 - 1 / (n + 1 : ℝ)) * C ≤ f x - f x₀ := by
    intro n
    set t : ℝ := 1 / (n + 1 : ℝ) with ht
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have ht0 : 0 < t := by rw [ht]; positivity
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hn1]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have h := hf.2 (mem_univ x) (mem_univ x₀) ht0.le (by linarith : (0 : ℝ) ≤ 1 - t)
      (by ring)
    have hlow := hmin (t • x + (1 - t) • x₀)
    simp only [smul_eq_mul] at h
    rw [← hC] at h
    have h2 : t * ((1 - t) * C) ≤ t * (f x - f x₀) := by nlinarith [hlow, h]
    exact le_of_mul_le_mul_left h2 ht0
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / (n + 1 : ℝ)) * C) atTop (𝓝 ((1 - 0) * C)) := by
    exact ((tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat).mul
      tendsto_const_nhds)
  have := le_of_tendsto hlim (Eventually.of_forall key)
  simpa using this
