-- Prove2me | Theorems.Thm_lean_workbook_plus_62616
-- name    : lean_workbook_plus_62616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/383f89c0-ce00-4c21-9c09-b24995c49186
-- statement:
--   It is known that $a>0$ , $a^4=a+1$ . Prove that $a^7<a+3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62616 (a : ℝ) (ha : a > 0) (h : a^4 = a + 1) : a^7 < a + 3   :=  by sorry
