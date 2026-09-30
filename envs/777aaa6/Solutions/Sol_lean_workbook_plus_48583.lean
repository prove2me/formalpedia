-- Prove2me | solution 1 for lean_workbook_plus_48583
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:31:24.278003+00:00
-- url     : https://prove2.me/submissions/eea584b8-c389-4511-8688-f411b5235237

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (c : ℝ) (f : ℝ → ℝ) (L : ℝ) (h : c ≠ 0) :
    (∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x - L| < ε) →
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f (c * x) - L| < ε := by
  intro hf ε hε
  obtain ⟨δ, hδ, hfδ⟩ := hf ε hε
  have hc : 0 < |c| := abs_pos.mpr h
  refine ⟨δ / |c|, div_pos hδ hc, ?_⟩
  intro x hx
  apply hfδ
  rw [abs_mul, mul_comm]
  exact (lt_div_iff₀ hc).mp hx

#print axioms solution
