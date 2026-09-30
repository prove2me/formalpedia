-- Prove2me | solution 1 for lean_workbook_plus_16528
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:33:36.592066+00:00
-- url     : https://prove2.me/submissions/0b461246-73ae-4906-a75c-8a2768b3d1f0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution {a b c d b1 b2 : ℤ} (h : a * d - b * c ≠ 0)
    (h1 : a * d - b * c ∣ b1) (h2 : a * d - b * c ∣ b2) :
    ∃ x y, a * x + b * y = b1 ∧ c * x + d * y = b2 := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  refine ⟨d * u - b * v, a * v - c * u, ?_, ?_⟩ <;> ring

#print axioms solution
