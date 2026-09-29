-- Prove2me | Theorems.Thm_lean_workbook_plus_67828
-- name    : lean_workbook_plus_67828
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/dfb9fc1b-91e0-435b-9e76-1f78952a9a70
-- statement:
--   Let $4n+ 9 = a^2$ , for some integer $a$ . We have $n = \dfrac{a^2-9}{4}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67828 (n : ℤ) (hn: 4*n+9 = a^2) : n = (a^2-9)/4   :=  by sorry
