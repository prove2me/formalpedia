-- Prove2me | Theorems.Thm_lean_workbook_plus_22268
-- name    : lean_workbook_plus_22268
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b159a72f-72be-4b59-a79d-ab60b9cdc8e2
-- statement:
--   $(ab+bc+ca)(a^2+b^2+c^2+a+b+c)\le 6(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22268 : ∀ a b c : ℝ, (a * b + b * c + c * a) * (a ^ 2 + b ^ 2 + c ^ 2 + a + b + c) ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
