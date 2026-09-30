-- Prove2me | solution 1 for lean_workbook_plus_9418
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:55.840892+00:00
-- url     : https://prove2.me/submissions/f80ccbed-3aed-43a7-b236-5d360ee58390

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (p L : ℝ) : (∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Set.Ioo p δ → |f x - L| < ε) → ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Set.Ioo p δ → |f x| - |L| < ε := by
  intro h ε hε
  obtain ⟨δ, hδ, hx⟩ := h ε hε
  refine ⟨δ, hδ, fun x hxd => ?_⟩
  have h1 := hx x hxd
  have h2 : |f x| - |L| ≤ |f x - L| := abs_sub_abs_le_abs_sub (f x) L
  linarith
