-- Prove2me | solution 1 for QuantizedWeightLattices.sublevel_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:05:40.345838+00:00
-- url     : https://prove2.me/submissions/b34b1870-5cd7-45b9-b819-5a2f23137fcb

import Mathlib
import Definitions.Def_Bridges_QuantizedWeightLattices
open QuantizedWeightLattices Set in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : NNReal} {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hL : LipschitzWith L f)
    (Q : Quantizer E) (c : ℝ) :
    Convex ℝ {x : E | f x ≤ c - (L : ℝ) * Q.radius} ∧
      {x : E | f x ≤ c - (L : ℝ) * Q.radius} ⊆ {x : E | f (Q.toFun x) ≤ c} ∧
      {x : E | f (Q.toFun x) ≤ c} ⊆ {x : E | f x ≤ c + (L : ℝ) * Q.radius} ∧
      Convex ℝ {x : E | f x ≤ c + (L : ℝ) * Q.radius} := by
  -- quantization moves `f` by at most `L · radius`
  have hlip : ∀ x, |f (Q.toFun x) - f x| ≤ (L : ℝ) * Q.radius := by
    intro x
    have h1 := hL.dist_le_mul (Q.toFun x) x
    rw [Real.dist_eq, dist_eq_norm] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (Q.error_le x) L.coe_nonneg)
  -- sublevel sets of a convex function are convex
  have hconv : ∀ r, Convex ℝ {x : E | f x ≤ r} := by
    intro r
    have := hf.convex_le r
    simpa using this
  refine ⟨hconv _, fun x hx => ?_, fun x hx => ?_, hconv _⟩
  · have := (abs_le.1 (hlip x)).2
    simp only [mem_setOf_eq] at hx ⊢
    linarith
  · have := (abs_le.1 (hlip x)).1
    simp only [mem_setOf_eq] at hx ⊢
    linarith
