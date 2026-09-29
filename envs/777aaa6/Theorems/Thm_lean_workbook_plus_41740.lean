-- Prove2me | Theorems.Thm_lean_workbook_plus_41740
-- name    : lean_workbook_plus_41740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d6044bbb-c89e-45f1-b8de-be8ef5319151
-- statement:
--   Find $ a$ such that $ f(0) = a^2 - 2a + 2 = 11$ in case 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41740 (a : ℝ) (h₁ : a^2 - 2*a + 2 = 11) : a = 1 - Real.sqrt 10 ∨ a = 1 + Real.sqrt 10   :=  by sorry
