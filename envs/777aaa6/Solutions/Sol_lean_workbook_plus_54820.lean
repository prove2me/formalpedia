-- Prove2me | solution 1 for lean_workbook_plus_54820
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:02.848365+00:00
-- url     : https://prove2.me/submissions/50ba58a3-7ac6-49ef-b96b-191253a2f013

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℤ) (hx : x = 2) (h : y^2 = x - (x+3)/(x^2+1)) : y = -1 ∨ y = 1 := by
  intros
  aesop (config := {maxRuleApplications := 120})
