-- Prove2me | Theorems.Thm_lean_workbook_plus_65475
-- name    : lean_workbook_plus_65475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9c762320-a7fc-4d2d-ad08-89700021c2cf
-- statement:
--   $ \Leftrightarrow \left(\sqrt{\frac{2}{1+bc}}-1\right)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65475 {b c : ℝ} (hbc : b * c ≤ 1) :
  (Real.sqrt (2 / (1 + b * c)) - 1)^2 ≥ 0   :=  by sorry
