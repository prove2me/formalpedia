-- Prove2me | Theorems.Thm_lean_workbook_plus_68394
-- name    : lean_workbook_plus_68394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/eb11b613-c854-41e3-88ac-c949cd6502b9
-- statement:
--   $a^3+b^3+c^3-3abc=(a^2+b^2+c^2-ab-bc-ca)(a+b+c).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68394 : ∀ a b c : ℝ, a^3 + b^3 + c^3 - 3*a*b*c = (a^2 + b^2 + c^2 - a*b - b*c - c*a)*(a + b + c)   :=  by sorry
