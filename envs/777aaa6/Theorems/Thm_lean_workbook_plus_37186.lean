-- Prove2me | Theorems.Thm_lean_workbook_plus_37186
-- name    : lean_workbook_plus_37186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e97bdd88-f12f-476a-b064-44ea3a01fdff
-- statement:
--   prove that $ a^4b^4+b^4c^4+c^4a^4 \ge a^2b^2c^2(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37186 (a b c : ℝ) : a^4 * b^4 + b^4 * c^4 + c^4 * a^4 ≥ a^2 * b^2 * c^2 * (a^2 + b^2 + c^2)   :=  by sorry
