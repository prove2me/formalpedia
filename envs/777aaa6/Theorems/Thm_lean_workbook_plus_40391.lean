-- Prove2me | Theorems.Thm_lean_workbook_plus_40391
-- name    : lean_workbook_plus_40391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f7f7389f-3591-470b-87ae-8c2c176c9ff2
-- statement:
--   Prove $\frac{4-x}{x}+\frac{x}{4-x}\ge \frac{62}{9}-\frac{32x}{9}$ for $0<x<4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40391 (x : ℝ) (hx: 0 < x ∧ x < 4) : (4 - x) / x + x / (4 - x) ≥ 62 / 9 - 32 * x / 9   :=  by sorry
