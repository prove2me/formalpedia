-- Prove2me | Theorems.Thm_lean_workbook_plus_82619
-- name    : lean_workbook_plus_82619
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/621c9aeb-6d14-4f80-80a2-f1b7ba5b04f4
-- statement:
--   Compute the value of $(1\\times 2)+(3\\times 4)+(5\\times 6)+...+(99\\times100)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82619 : ∑ n in Finset.range 50, (2 * n + 1) * (2 * n + 2) = 24500   :=  by sorry
