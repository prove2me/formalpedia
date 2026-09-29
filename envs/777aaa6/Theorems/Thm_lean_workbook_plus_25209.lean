-- Prove2me | Theorems.Thm_lean_workbook_plus_25209
-- name    : lean_workbook_plus_25209
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5793e344-4fe6-49fd-b5d9-7eb9b0dee4d5
-- statement:
--   Using the formula for sum of first $n$ squares yields $\sum_{k=1}^{99} k^2=\frac{99(100)(199)}{6}=33(50)(199)$ . Now the remainder of a number modulo 9 is the sum of its digits, hence $33(50)(199)\equiv 6(5)(19)\equiv 30\equiv \boxed{3}\pmod 9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25209 :
  (∑ k in (Finset.range 99), k^2) % 9 = 3   :=  by sorry
