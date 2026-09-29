-- Prove2me | Theorems.Thm_lean_workbook_plus_18415
-- name    : lean_workbook_plus_18415
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5b8f3d0a-2941-4445-872a-9ff8dc2540b5
-- statement:
--   Every day, the clock chimes $ 2 \left(1 + 2 + \cdots + 12\right) + 24 = 12 \cdot 13 + 24 = 180 \text{ times.}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18415 2 * (∑ k in Finset.Icc 1 12, k) + 24 = 180   :=  by sorry
