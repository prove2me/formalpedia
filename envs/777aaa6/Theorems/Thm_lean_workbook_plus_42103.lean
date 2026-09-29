-- Prove2me | Theorems.Thm_lean_workbook_plus_42103
-- name    : lean_workbook_plus_42103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f93dd0f6-0ccd-4d0f-96f3-d84e0041ee90
-- statement:
--   Let $r$ and $b$ be the fraction of red and blue knights that are magical, respectively. Then, $2r/7+5b/7=1/6$ and $r=2b.$ Substituting, we have $9b/7=1/6\implies b=7/54.$ Thus, $r=\boxed{\text{C}~7/27}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42103  (r b : ℚ)
  (h₀ : 0 < r ∧ 0 < b)
  (h₁ : r = 2 * b)
  (h₂ : (2 * r / 7 + 5 * b / 7) = 1 / 6) :
  r = 7 / 27   :=  by sorry
