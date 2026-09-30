-- Prove2me | solution 1 for lean_workbook_plus_44988
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:31:33.476713+00:00
-- url     : https://prove2.me/submissions/555ac81b-dba0-4cac-bb00-bbb48da16400

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (f : ℝ → ℝ)
    (h : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x + f (2 * x)| < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := h (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro x hx
  have hxδ : |x| < δ := by linarith
  have h2xδ : |2 * x| < δ := by
    rw [abs_mul]
    norm_num
    linarith
  have hx' := hfδ x hxδ
  have h2x' := hfδ (2 * x) h2xδ
  exact (abs_add_le (f x) (f (2 * x))).trans_lt (by linarith)

#print axioms solution
