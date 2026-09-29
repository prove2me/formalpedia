-- Prove2me | Theorems.Thm_lean_workbook_plus_76116
-- name    : lean_workbook_plus_76116
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e36ae1ab-c23b-4517-bcd0-8e8cfdc0d40b
-- statement:
--   so in the case, we have $7 \cdot 15 + 20 \cdot 24 = 105 + 480 = 585 = 25x \ \ x = \frac{117}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76116  (x : ℝ)
  (h₀ : 7 * 15 + 20 * 24 = 25 * x) :
  x = 117 / 5   :=  by sorry
