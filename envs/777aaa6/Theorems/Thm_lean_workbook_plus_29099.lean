-- Prove2me | Theorems.Thm_lean_workbook_plus_29099
-- name    : lean_workbook_plus_29099
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0e6c9ed2-13e6-4837-8ff2-399362de0170
-- statement:
--   Dividing by $ 4$ ,we have that $ \frac {a}{4} + \frac {b}{4} + \frac {c}{4} = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29099 {a b c : ℝ} (h : a + b + c = 4) : a / 4 + b / 4 + c / 4 = 1   :=  by sorry
