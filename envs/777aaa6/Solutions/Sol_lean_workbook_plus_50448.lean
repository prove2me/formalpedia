-- Prove2me | solution 1 for lean_workbook_plus_50448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:38.987009+00:00
-- url     : https://prove2.me/submissions/0b42a640-272c-4fad-86b5-f045a34c5b9a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℕ) (h : a < 462) (ha : Nat.Coprime 462 a) : Nat.Coprime 462 (a + 462) := by
  intros
  aesop (config := {maxRuleApplications := 120})
