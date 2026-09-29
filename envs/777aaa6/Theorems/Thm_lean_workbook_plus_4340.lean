-- Prove2me | Theorems.Thm_lean_workbook_plus_4340
-- name    : lean_workbook_plus_4340
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/41bef039-b73a-4868-ab12-7fd1ddf8ebc2
-- statement:
--   Show that $\log_32^{102} = 102 \log_32$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4340 : Real.logb 3 (2^102) = 102 * Real.logb 3 2   :=  by sorry
