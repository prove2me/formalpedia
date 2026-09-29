-- Prove2me | Theorems.Thm_lean_workbook_plus_77092
-- name    : lean_workbook_plus_77092
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6a197dff-9eb0-4b07-8998-e434d8f72135
-- statement:
--   Find the coefficient of the $y^2$ term of each power of each binomial, which by the binomial theorem is ${2\choose 2} + {3\choose 2} + \cdots + {17\choose 2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77092 ∑ k in Finset.Icc 2 17, (k.choose 2) = 816   :=  by sorry
