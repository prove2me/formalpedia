-- Prove2me | Theorems.Thm_lean_workbook_plus_44987
-- name    : lean_workbook_plus_44987
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/68c8ff47-d0a3-47f7-8b27-e8f43a4ce40f
-- statement:
--   a. $ a-b=a+(-b) $ ; also,if b $\neq $ 0, then $ a/b=ab^{-1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44987 {a b : ℝ} (h : b ≠ 0) : a - b = a + -b   :=  by sorry
