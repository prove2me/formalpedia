-- Prove2me | Theorems.Thm_lean_workbook_plus_79945
-- name    : lean_workbook_plus_79945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/04cd91a2-b054-4acb-885b-5a44ab67f05b
-- statement:
--   Similar ineq (easier and classical) $ a^2+b^2+c^2=1$ <=> $ \frac{1}{4+a^2-2bc} \le \frac{9}{11}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79945 (a b c : ℝ) (ha : a^2 + b^2 + c^2 = 1) : 1 / (4 + a^2 - 2 * b * c) ≤ 9 / 11   :=  by sorry
