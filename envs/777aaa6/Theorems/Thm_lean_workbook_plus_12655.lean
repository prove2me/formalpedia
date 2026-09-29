-- Prove2me | Theorems.Thm_lean_workbook_plus_12655
-- name    : lean_workbook_plus_12655
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/240c0f94-5e27-4454-85aa-dc363c0d87bd
-- statement:
--   So, the series reduces to $1^2 + 2^2 + 3^2 + ... + 50^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12655 : ∑ i in Finset.range 51, (i + 1)^2 = 13325   :=  by sorry
