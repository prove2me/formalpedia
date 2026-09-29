-- Prove2me | Theorems.Thm_lean_workbook_plus_55695
-- name    : lean_workbook_plus_55695
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/1d08b1fe-7109-4838-b2e2-f5b7f0b40a99
-- statement:
--   Prove that $\sqrt{a}+\sqrt{b} \le \sqrt{2(a+b)}$ using AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55695 (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b) : Real.sqrt a + Real.sqrt b ≤ Real.sqrt (2 * (a + b))   :=  by sorry
