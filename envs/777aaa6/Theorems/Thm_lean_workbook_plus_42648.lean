-- Prove2me | Theorems.Thm_lean_workbook_plus_42648
-- name    : lean_workbook_plus_42648
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/74ee1353-0764-4b51-96bc-fe576606596e
-- statement:
--   Let $x = \dfrac{1 + \sqrt{5}}{2}$ . Thus $2x - 1 = \sqrt{5}$ . Squaring, $4x^2 - 4x + 1 = 5$ , or $4x^2 - 4x - 4 = 0$ , or $\boxed{x^2 - x - 1 = 0}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42648  (x : ℝ)
  (h₀ : x = (1 + Real.sqrt 5) / 2) :
  x^2 - x - 1 = 0   :=  by sorry
