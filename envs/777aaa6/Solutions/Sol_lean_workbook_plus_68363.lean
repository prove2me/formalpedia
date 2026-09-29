-- Prove2me | solution 1 for lean_workbook_plus_68363
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:02:50.477797+00:00
-- url     : https://prove2.me/submissions/aa7a7f42-4c94-480c-b23d-4c34815ea5ac

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (p q s : Prop) (h₁ : p → s) (h₂ : q → s) : p ∨ q → s := by
  intros
  aesop (config := {maxRuleApplications := 120})
