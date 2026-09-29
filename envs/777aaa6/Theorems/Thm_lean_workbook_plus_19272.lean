-- Prove2me | Theorems.Thm_lean_workbook_plus_19272
-- name    : lean_workbook_plus_19272
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c8ec6563-3f30-486a-a02c-5c3c8873982a
-- statement:
--   In that case, we can write\n\n $6 \cdot 3 \cdot x = 4 \cdot 9 \cdot 3$\n\n $18x = 36 \cdot 3$\n\n $x = 2 \cdot 3 = \boxed{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19272  (x : ℝ)
  (h₀ : 6 * 3 * x = 4 * 9 * 3) :
  x = 6   :=  by sorry
