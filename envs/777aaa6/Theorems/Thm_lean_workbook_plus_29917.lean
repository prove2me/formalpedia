-- Prove2me | Theorems.Thm_lean_workbook_plus_29917
-- name    : lean_workbook_plus_29917
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0bb7e0f0-0cd8-4b1f-97a4-3a3c1a665ccc
-- statement:
--   Set the sum to $S$ , then $2S=1+\frac{3}{2}+\frac{5}{2^2}+\frac{7}{2^3}+...+\frac{45}{2^{22}}$ , and subtracting gives $S=1+1+\frac{1}{2}+\frac{1}{2^2}+...+\frac{1}{2^{21}}-\frac{45}{2^{23}}=\boxed{3-\frac{49}{2^{23}}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29917 :
  ∑ k in (Finset.range 23), (1 / (2^k)) - 45 / (2^23) = 3 - 49 / (2^23)   :=  by sorry
