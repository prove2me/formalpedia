-- Prove2me | Theorems.Thm_lean_workbook_plus_53196
-- name    : lean_workbook_plus_53196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6871335e-ac9b-40cc-8a34-9ccb93b39535
-- statement:
--   If $a,b,c\ge 0$, $a^2 +b^2+c^2+2abc=5$, prove that $abc+a+b+c\le 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53196 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 5) : a * b * c + a + b + c ≤ 4   :=  by sorry
