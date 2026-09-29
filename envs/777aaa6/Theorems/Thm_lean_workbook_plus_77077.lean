-- Prove2me | Theorems.Thm_lean_workbook_plus_77077
-- name    : lean_workbook_plus_77077
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8ad62017-0c64-40f3-ab95-200844db0093
-- statement:
--   Find the value of $\sum^{10}_{r=1}r\cdot \binom{10}{r}^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77077 (h₁ : 0 < 10) : ∑ r in Finset.Icc 1 10, r * (Nat.choose 10 r)^2 = 4620   :=  by sorry
