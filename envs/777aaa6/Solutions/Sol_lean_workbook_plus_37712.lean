-- Prove2me | solution 1 for lean_workbook_plus_37712
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:58.868963+00:00
-- url     : https://prove2.me/submissions/f7c92df1-f94b-4c06-9629-3ffc72c5e824

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (h : ∃ k, k^2 = n) : √n - ⌊√n⌋ = 0 := by
  intros
  aesop (config := {maxRuleApplications := 120})
