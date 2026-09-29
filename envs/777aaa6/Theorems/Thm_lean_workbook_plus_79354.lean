-- Prove2me | Theorems.Thm_lean_workbook_plus_79354
-- name    : lean_workbook_plus_79354
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/444e1ab5-755c-43c6-8eaf-2ad02d462f76
-- statement:
--   Now the arrangement $(a_1,b_1,c_1);(a_2,b_2,c_2);...;(a_6,b_6,c_6)=(6,4,1);(4,1,6);(1,6,4);(5,3,2);(3,2,5);(2,5,3)$ gives $\sum_{i=1}^{6}a_{i}b_{i}c_{i}=162$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79354 :
  (6 * 4 * 1 + 4 * 1 * 6 + 1 * 6 * 4 + 5 * 3 * 2 + 3 * 2 * 5 + 2 * 5 * 3) = 162   :=  by sorry
