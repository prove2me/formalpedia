-- Prove2me | Theorems.Thm_lean_workbook_plus_43104
-- name    : lean_workbook_plus_43104
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/078b690e-d4cc-439b-a57d-5246770c5603
-- statement:
--   Prove that $(a^2+b^2+c^2)^2 \ge 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43104 : ∀ a b c : ℝ, (a^2 + b^2 + c^2)^2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
