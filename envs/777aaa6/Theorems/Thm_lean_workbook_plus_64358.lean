-- Prove2me | Theorems.Thm_lean_workbook_plus_64358
-- name    : lean_workbook_plus_64358
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/99ff2de5-5aee-491d-b1ab-752da27edf69
-- statement:
--   Let $M$ be composed of the number 1 and all non-negative numbers being divisible by 5. Let $\bar{i} = 0,1,2,3,4$ be the residue class $i$ modulo 5 in $\mathbb{Z}$ . Then we can represent $M$ as $M = \bar{0} \cup \{1\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64358 {m : ℤ | m % 5 = 0 ∨ m = 1} = {m : ℤ | m % 5 = 0} ∪ {1}   :=  by sorry
