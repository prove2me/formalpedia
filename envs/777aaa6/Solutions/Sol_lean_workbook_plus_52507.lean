-- Prove2me | solution 1 for lean_workbook_plus_52507
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:36.139613+00:00
-- url     : https://prove2.me/submissions/f20a04dc-7689-4e88-bca1-4fed81b47bbb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h : a + b + c = 0) :
    ∃ x : ℤ, x ^ 2 = 2 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  refine ⟨a ^ 2 + b ^ 2 + c ^ 2, ?_⟩
  have hc : c = -(a + b) := by omega
  rw [hc]
  ring

#print axioms solution
