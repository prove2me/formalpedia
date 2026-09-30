-- Prove2me | solution 1 for lean_workbook_plus_28377
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:41:00.504159+00:00
-- url     : https://prove2.me/submissions/4e32d33a-7979-4dc6-af83-f33383b7b395

import Mathlib.Analysis.Complex.Basic

theorem solution {g h f : ℝ → ℝ} {a b : ℝ} (hg : ContinuousAt g a) (hh : ContinuousAt h a) (hg' : g a = b) (hh' : h a = b)
  (hf : ∀ x, (x ∈ Set.range ((↑) : ℚ → ℝ) ↔ f x = g x) ∧ (x ∉ Set.range ((↑) : ℚ → ℝ) ↔ f x = h x)) :
  ContinuousAt f a := by
  have key : ∀ x, f x = g x ∨ f x = h x := by
    intro x
    by_cases hx : x ∈ Set.range ((↑) : ℚ → ℝ)
    · exact Or.inl ((hf x).1.mp hx)
    · exact Or.inr ((hf x).2.mp hx)
  have hfa : f a = b := by
    rcases key a with h1 | h1
    · rw [h1, hg']
    · rw [h1, hh']
  rw [ContinuousAt, hfa, Metric.tendsto_nhds]
  intro ε hε
  have h1 := Metric.tendsto_nhds.mp hg ε hε
  have h2 := Metric.tendsto_nhds.mp hh ε hε
  rw [hg'] at h1
  rw [hh'] at h2
  filter_upwards [h1, h2] with x hx1 hx2
  rcases key x with h3 | h3
  · rw [h3]; exact hx1
  · rw [h3]; exact hx2
