-- Prove2me | Theorems.Thm_lean_workbook_plus_1696
-- name    : lean_workbook_plus_1696
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/575973f9-ca1e-40a8-bc24-8e2797a020cb
-- statement:
--   If $ a,b,c$ are positive numbers less than 1, then \n\n $ (1+a)(1+b)(1+c) \ge 2(1+a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1696 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) : (1 + a) * (1 + b) * (1 + c) ≥ 2 * (1 + a + b + c)   :=  by sorry
