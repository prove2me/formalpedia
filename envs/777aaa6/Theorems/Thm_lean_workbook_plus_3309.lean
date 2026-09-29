-- Prove2me | Theorems.Thm_lean_workbook_plus_3309
-- name    : lean_workbook_plus_3309
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4ecbede2-e1ae-48fd-8918-9af11144d4de
-- statement:
--   Suppose that $4^a=5$ , $5^b=6$ , $6^c=7$ , and $7^d=8$ . What is $a\cdot b\cdot c\cdot d$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3309 (a b c d : ℝ) (h1 : (4:ℝ)^a = 5) (h2 : (5:ℝ)^b = 6) (h3 : (6:ℝ)^c = 7) (h4 : (7:ℝ)^d = 8) : a*b*c*d = 3/2   :=  by sorry
