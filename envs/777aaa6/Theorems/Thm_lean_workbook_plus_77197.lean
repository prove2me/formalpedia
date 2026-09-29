-- Prove2me | Theorems.Thm_lean_workbook_plus_77197
-- name    : lean_workbook_plus_77197
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d3b69c02-f734-4f0d-9fc2-c4a9d062d32e
-- statement:
--   prove that: $3/8\, \left( yz-{x}^{2} \right) ^{2}{y}^{2}+3/8\, \left( xz-{y}^{2} \right) ^{2}{z}^{2}+3/8\, \left( xy-{z}^{2} \right) ^{2}{x}^{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77197 (x y z : ℝ) :
  3 / 8 * (y * z - x ^ 2) ^ 2 * y ^ 2 + 3 / 8 * (x * z - y ^ 2) ^ 2 * z ^ 2 + 3 / 8 * (x * y - z ^ 2) ^ 2 * x ^ 2 ≥ 0   :=  by sorry
