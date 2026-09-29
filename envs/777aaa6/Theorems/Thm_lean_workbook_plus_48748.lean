-- Prove2me | Theorems.Thm_lean_workbook_plus_48748
-- name    : lean_workbook_plus_48748
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b2ef956f-3d7e-4ff1-b134-2b94aeedca53
-- statement:
--   We reduce again and finally we obtain the inequality: $ (a^4b^2+1)+(a^2b^4+1)+(a^4c^2+1)+(a^2c^4+1)+(b^4c^2+1)+(b^2c^4+1)+(a^3b^3+a^3c^3)+(b^3a^3+b^3c^3)+(c^3a^3+c^3b^3) \ge 2a^2b+2ab^2+2a^2c+2ac^2+2b^2c+2bc^2+2a^3+2b^3+2c^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48748 : ∀ a b c : ℝ, (a^4 * b^2 + 1) + (a^2 * b^4 + 1) + (a^4 * c^2 + 1) + (a^2 * c^4 + 1) + (b^4 * c^2 + 1) + (b^2 * c^4 + 1) + (a^3 * b^3 + a^3 * c^3) + (b^3 * a^3 + b^3 * c^3) + (c^3 * a^3 + c^3 * b^3) ≥ 2 * a^2 * b + 2 * a * b^2 + 2 * a^2 * c + 2 * a * c^2 + 2 * b^2 * c + 2 * b * c^2 + 2 * a^3 + 2 * b^3 + 2 * c^3   :=  by sorry
