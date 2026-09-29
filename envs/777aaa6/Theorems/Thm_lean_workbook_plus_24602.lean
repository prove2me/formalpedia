-- Prove2me | Theorems.Thm_lean_workbook_plus_24602
-- name    : lean_workbook_plus_24602
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d1b49dc0-21c9-4838-9e76-9e50b8de2560
-- statement:
--   You have calculated the permutations, which is $12\times 10\times 8\times 6\times 4=23040.$ You don't care about arrangement, so you divide by $\left(6-1\right)!=5!$ to get $\frac{12\times 10\times 8\times 6\times 4}{5!}=192=\binom{6}{5}2^{5}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24602 :
  12 * 10 * 8 * 6 * 4 / (5!) = 192   :=  by sorry
