-- Prove2me | solution 1 for lean_workbook_plus_76831
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:02.635788+00:00
-- url     : https://prove2.me/submissions/85d3a806-0f03-4ff7-80a9-6d2ceac4c2ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (x y z : ℤ) : (x^2 + x + 1) ∣ (x^7 + x^2 + 1) := by
  refine ⟨x ^ 5 - x ^ 4 + x ^ 2 - x + 1, ?_⟩
  ring

#print axioms solution
