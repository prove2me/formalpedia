-- Prove2me | solution 1 for lean_workbook_plus_20489
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:34.109697+00:00
-- url     : https://prove2.me/submissions/bf40e43d-3d22-43f7-99a5-1cdd71bed40d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (f g : ℝ → ℝ) (a F G : ℝ)
    (hf : ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a ∧ |x - a| < δ → |f x - F| < ε)
    (hg : ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a ∧ |x - a| < δ → |g x - G| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ a ∧ |x - a| < δ → |f x + g x - (F + G)| < ε := by
  intro ε hε
  obtain ⟨δf, hδf, hfδ⟩ := hf (ε / 2) (by linarith)
  obtain ⟨δg, hδg, hgδ⟩ := hg (ε / 2) (by linarith)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro x hx
  have hfx := hfδ x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hgx := hgδ x ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
  calc
    |f x + g x - (F + G)| = |(f x - F) + (g x - G)| := by congr 1; ring
    _ ≤ |f x - F| + |g x - G| := abs_add_le _ _
    _ < ε := by linarith

#print axioms solution
