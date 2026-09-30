-- Prove2me | solution 1 for lean_workbook_plus_36683
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:12.895933+00:00
-- url     : https://prove2.me/submissions/ebe72628-5d5f-4ec4-be45-5abfa1256c3f

import Mathlib.Analysis.Complex.Basic

theorem solution :
  ∀ x y z : ℝ,
    0 < x ∧ 0 < y ∧ 0 < z →
    x ≤ y ∧ y ≤ z ∧ z ≤ x →
    0 ≤ (x - y) * (x - z) * (y - z) * (x + y + z) / (x + y) / (x + z) / (y + z) := by
  intro x y z _ ⟨h1, h2, h3⟩
  have hxy : x = y := le_antisymm h1 (le_trans h2 h3)
  subst hxy
  simp
