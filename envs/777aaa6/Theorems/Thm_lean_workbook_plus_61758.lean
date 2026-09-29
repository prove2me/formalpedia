-- Prove2me | Theorems.Thm_lean_workbook_plus_61758
-- name    : lean_workbook_plus_61758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5a473ccc-29c9-440f-a7e8-f7f835997b69
-- statement:
--   First note that since $ab=1,$ we have $a^nb^n=a^{n-1}(ab)b^{n-1}=a^{n-1}b^{n-1}= \cdots =ab=1, \ \ \ \ \ \ \ \ \ \ (*)$ for all integers $n \ge 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61758 {a b : ℤ} (hab : a * b = 1) (n : ℕ) : a ^ n * b ^ n = 1   :=  by sorry
