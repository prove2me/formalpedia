-- Prove2me | Theorems.Thm_lean_workbook_plus_74487
-- name    : lean_workbook_plus_74487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/cb9489ec-189a-4603-8ced-2d21dc739c7e
-- statement:
--   Let $ a \ge 0$ such that : $ a - a^3 + a^5 \ge 3$ , Prove that : $ a^6 \ge 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74487 (a : ℝ) (ha : a - a^3 + a^5 >= 3) : a^6 >= 5   :=  by sorry
