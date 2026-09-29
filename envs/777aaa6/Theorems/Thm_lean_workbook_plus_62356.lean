-- Prove2me | Theorems.Thm_lean_workbook_plus_62356
-- name    : lean_workbook_plus_62356
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4e5d3380-d1cb-4461-b390-86bca5b5106c
-- statement:
--   Prove that $abc \ge \frac{{4\left( {ab + bc + ca} \right)\left( {a + b + c} \right) - {{\left( {a + b + c} \right)}^3}}}{9}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62356 : ∀ a b c : ℝ, a * b * c ≥ (4 * (a * b + b * c + c * a) * (a + b + c) - (a + b + c) ^ 3) / 9   :=  by sorry
