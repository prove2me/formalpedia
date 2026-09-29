-- Prove2me | Theorems.Thm_lean_workbook_plus_12440
-- name    : lean_workbook_plus_12440
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/540694f5-c20a-4d84-a19b-68edc101a7c8
-- statement:
--   Let $a<b$. Prove that if $20(b-a)<2$, then $20(b-a)\neq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12440 : 20 * (b - a) < 2 → 20 * (b - a) ≠ 1   :=  by sorry
