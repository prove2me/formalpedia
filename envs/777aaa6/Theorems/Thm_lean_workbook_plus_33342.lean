-- Prove2me | Theorems.Thm_lean_workbook_plus_33342
-- name    : lean_workbook_plus_33342
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/91b602fe-4286-4a68-890b-c6d7b91c7dc0
-- statement:
--   There are $\binom{12}{3}=220$ ways of ordering the balloons, and we have to divide by 2 to account for symmetry. Thus, the answer is $\frac{220}{2}=\boxed{110}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33342 (Nat.choose 12 3)/2 = 110   :=  by sorry
