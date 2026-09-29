-- Prove2me | Theorems.Thm_lean_workbook_plus_47740
-- name    : lean_workbook_plus_47740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/8f6cd8c7-6bb5-45f6-8e04-2c17e10819d5
-- statement:
--   For positive real numbers a, b, c, prove that \n $ (a^{2}+b^{2})^{2}\geq (a+b+c)(a+b-c)(b+c-a)(c+a-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47740 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b)   :=  by sorry
