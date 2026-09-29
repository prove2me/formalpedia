-- Prove2me | Theorems.Thm_lean_workbook_plus_58461
-- name    : lean_workbook_plus_58461
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/dcae18c4-055f-462a-96c4-29be3f479784
-- statement:
--   Lemma 2.\n $(a^3+b^3+c^3)(ab+bc+ca)^2\geq 3abc(a^2+b^2+c^2)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58461 : ∀ a b c : ℝ, (a^3 + b^3 + c^3) * (a * b + b * c + c * a)^2 ≥ 3 * a * b * c * (a^2 + b^2 + c^2)^2   :=  by sorry
