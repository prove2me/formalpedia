-- Prove2me | Theorems.Thm_lean_workbook_plus_5613
-- name    : lean_workbook_plus_5613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e35b8e41-cb31-4766-96a6-a82b5a45b3aa
-- statement:
--   Prove that $x^8+x^7+x^6-x^5+x^3-x^2+1\geq0$ for all real numbers $x$ in the interval $(0, 1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5613 (x : ℝ) (hx : 0 < x ∧ x < 1) :
  x^8 + x^7 + x^6 - x^5 + x^3 - x^2 + 1 ≥ 0   :=  by sorry
