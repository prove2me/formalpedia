-- Prove2me | Theorems.Thm_lean_workbook_plus_13855
-- name    : lean_workbook_plus_13855
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/62ab7e38-7551-4e29-a102-c66f5b2271c4
-- statement:
--   Find the value of $1^2 \cdot 0 + 0^2 \cdot 1 + 0^2 \cdot 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13855 (h : 0^2 = 0) : 1^2 * 0 + 0^2 * 1 + 0^2 * 1 = 0   :=  by sorry
