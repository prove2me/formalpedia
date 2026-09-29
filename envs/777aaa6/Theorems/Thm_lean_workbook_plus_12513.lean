-- Prove2me | Theorems.Thm_lean_workbook_plus_12513
-- name    : lean_workbook_plus_12513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/8e4f7722-25d3-42a5-989e-408e19261a24
-- statement:
--   $5^{51}\ge2^{118}\Longleftrightarrow \left(1-\dfrac{3}{128}\right)^{17}\ge\dfrac12$ which is obvious by Bernoulli.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12513 : (5 : ℝ)^(51) ≥ 2^(118) ↔ (1 - 3 / 128)^(17) ≥ 1 / 2   :=  by sorry
