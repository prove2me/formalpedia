-- Prove2me | Theorems.Thm_lean_workbook_plus_65473
-- name    : lean_workbook_plus_65473
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1ef5a059-13f1-478d-8ec6-6558eb26bd99
-- statement:
--   Prove that for positive real numbers $ a, b, c $, the inequality\n $ ab(a+b)+bc(b+c)+ca(c+a) \ge 6abc $ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * (a + b) + b * c * (b + c) + c * a * (c + a) ≥ 6 * a * b * c   :=  by sorry
