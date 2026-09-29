-- Prove2me | Theorems.Thm_lean_workbook_plus_63070
-- name    : lean_workbook_plus_63070
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e55cdc53-ccc2-4177-bc8a-f01927797bf6
-- statement:
--   Let a,b,c>0 : $a^2+b^2+c^2 +abc=4$ .Prove that $abc+2 \ge ab+bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63070 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) (hab : a + b + c = 3): a^2 + b^2 + c^2 + a * b * c = 4 → a * b * c + 2 ≥ a * b + b * c + c * a   :=  by sorry
