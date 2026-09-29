-- Prove2me | Theorems.Thm_lean_workbook_plus_40764
-- name    : lean_workbook_plus_40764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0f4bb7b2-4a82-428e-87c6-fa528f507788
-- statement:
--   Prove that $32b^4 + 35b^2c^2 - 44b^3c - 18bc^3 + 27c^4\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40764 (b c : ℝ) :
  32 * b^4 + 35 * b^2 * c^2 - 44 * b^3 * c - 18 * b * c^3 + 27 * c^4 ≥ 0   :=  by sorry
