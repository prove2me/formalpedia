-- Prove2me | Theorems.Thm_lean_workbook_plus_30908
-- name    : lean_workbook_plus_30908
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/03ebdbfa-85b4-4872-a4e3-b3ee1b7e7d87
-- statement:
--   The inequality $\frac{2z}{\frac{1}{z} + z} \geq 1$ when $z\geq1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30908 : ∀ z : ℝ, 1 ≤ z → 2 * z / (1 / z + z) ≥ 1   :=  by sorry
