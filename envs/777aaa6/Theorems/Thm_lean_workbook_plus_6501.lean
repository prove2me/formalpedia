-- Prove2me | Theorems.Thm_lean_workbook_plus_6501
-- name    : lean_workbook_plus_6501
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b49a410e-e08e-4154-acc0-cea3e4e7127d
-- statement:
--   Prove that $2(a^4+b^4)(b^4+c^4)(c^4+a^4) \geq (ab^2+bc^2+ca^2-abc)^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6501 : ∀ a b c : ℝ, 2 * (a ^ 4 + b ^ 4) * (b ^ 4 + c ^ 4) * (c ^ 4 + a ^ 4) ≥ (a * b ^ 2 + b * c ^ 2 + c * a ^ 2 - a * b * c) ^ 4   :=  by sorry
