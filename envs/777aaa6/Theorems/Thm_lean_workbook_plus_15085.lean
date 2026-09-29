-- Prove2me | Theorems.Thm_lean_workbook_plus_15085
-- name    : lean_workbook_plus_15085
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f85a7547-eefb-4618-8a54-3fd0bdae2b0a
-- statement:
--   $2\cdot 3(a^2+b^2+c^2)^2 \geq (a+b+c)^2 (a^2+b^2+c^2+ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15085 (a b c : ℝ) :
  2 * 3 * (a^2 + b^2 + c^2)^2 ≥ (a + b + c)^2 * (a^2 + b^2 + c^2 + a * b + b * c + c * a)   :=  by sorry
