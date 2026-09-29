-- Prove2me | Theorems.Thm_lean_workbook_plus_170
-- name    : lean_workbook_plus_170
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8c50e1d5-c351-41a7-bd32-d4cf07b718b7
-- statement:
--   $\frac{ab+bc+ca}{4} \ge (s-b)(s-c)+(s-a)(s-b)+(s-c)(s-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_170 {a b c s : ℝ} (hs : s = (a + b + c) / 2) : (a * b + b * c + c * a) / 4 ≥ (s - b) * (s - c) + (s - a) * (s - b) + (s - c) * (s - a)   :=  by sorry
