-- Prove2me | Theorems.Thm_lean_workbook_plus_42361
-- name    : lean_workbook_plus_42361
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2c64de92-cc5e-4984-bec5-7787c2742d1c
-- statement:
--   Prove that the following inequality holds: $\frac{a_1^2}{b_1}+\frac{a_2^2}{b_2}\ge\frac{(a_1+a_2)^2}{b_1+b_2}$ for all positive reals $a_1, a_2, b_1, b_2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42361 (a1 a2 b1 b2 : ℝ) (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 < b1) (hb2 : 0 < b2) : (a1 ^ 2 / b1 + a2 ^ 2 / b2) ≥ (a1 + a2) ^ 2 / (b1 + b2)   :=  by sorry
