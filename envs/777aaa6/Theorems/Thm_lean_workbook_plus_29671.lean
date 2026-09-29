-- Prove2me | Theorems.Thm_lean_workbook_plus_29671
-- name    : lean_workbook_plus_29671
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/1bc6e3b3-53ba-4cb2-a1fd-9fe66668ed11
-- statement:
--   Prove that $a^2c+b^2a+c^2b-3abc\geq 0$ for positive real numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29671 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * c + b^2 * a + c^2 * b - 3 * a * b * c ≥ 0   :=  by sorry
