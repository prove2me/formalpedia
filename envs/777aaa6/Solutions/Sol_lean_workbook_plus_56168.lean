-- Prove2me | solution 1 for lean_workbook_plus_56168
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:16.01615+00:00
-- url     : https://prove2.me/submissions/f5e0c9ac-5de8-42f6-a130-d10fd81a2485

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution {a b c : ℤ} (h : a + b + c = 0) :
    (a^2 + b^2 + c^2) ∣ (a^4 + b^4 + c^4) := by
  have hc : c = -a - b := by omega
  rw [hc]
  refine ⟨a ^ 2 + a * b + b ^ 2, ?_⟩
  ring

#print axioms solution
