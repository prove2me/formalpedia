-- Prove2me | Theorems.Thm_lean_workbook_plus_76771
-- name    : lean_workbook_plus_76771
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/9915dfc5-f487-4056-ad3e-52a29bbfe3b3
-- statement:
--   Prove that $12(x^{2}-xy+y^{2})a^{2}+3(4x^{3}+5x^{2}y-9xy^{2}+4y^{3})a+4x^{4}+5x^{3}y-9xy^{3}+4y^{4}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76771 : ∀ x y a : ℝ, 12 * (x ^ 2 - x * y + y ^ 2) * a ^ 2 + 3 * (4 * x ^ 3 + 5 * x ^ 2 * y - 9 * x * y ^ 2 + 4 * y ^ 3) * a + 4 * x ^ 4 + 5 * x ^ 3 * y - 9 * x * y ^ 3 + 4 * y ^ 4 ≥ 0   :=  by sorry
