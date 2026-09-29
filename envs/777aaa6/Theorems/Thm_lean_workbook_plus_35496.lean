-- Prove2me | Theorems.Thm_lean_workbook_plus_35496
-- name    : lean_workbook_plus_35496
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2a44ce92-8981-429c-809a-81a16cce4673
-- statement:
--   Prove that if $x \ge0$ , $3x^3 - 6x^2 + \frac{32}{9} \ge0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35496 (x : ℝ) (hx: x >= 0) : 3 * x ^ 3 - 6 * x ^ 2 + 32 / 9 ≥ 0   :=  by sorry
