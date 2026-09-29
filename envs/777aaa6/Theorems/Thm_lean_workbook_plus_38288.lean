-- Prove2me | Theorems.Thm_lean_workbook_plus_38288
-- name    : lean_workbook_plus_38288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/8744df2b-7013-4aa5-8e80-d3b531d48aa8
-- statement:
--   Prove that $2x^5-5x^2+3 \geq 0$ if $x \geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38288 (x : ℝ) (hx : x ≥ 0) : 2 * x ^ 5 - 5 * x ^ 2 + 3 ≥ 0   :=  by sorry
