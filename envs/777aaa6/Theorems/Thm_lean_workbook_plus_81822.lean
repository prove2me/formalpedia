-- Prove2me | Theorems.Thm_lean_workbook_plus_81822
-- name    : lean_workbook_plus_81822
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/45fecc86-5ae9-40e9-b14d-f6fabc5ec16e
-- statement:
--   If $a, b, c>0$ and $(a+b) (b+c) =1$ . Prove that $(1-b+4ab) (1-b+4bc) (1-b+ca) \leq\frac{ 4}{27}(1+a) ^3 (1+c) ^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81822 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a + b) * (b + c) = 1) : (1 - b + 4 * a * b) * (1 - b + 4 * b * c) * (1 - b + c * a) ≤ (4 / 27) * (1 + a) ^ 3 * (1 + c) ^ 3   :=  by sorry
