-- Prove2me | Theorems.Thm_lean_workbook_plus_32820
-- name    : lean_workbook_plus_32820
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/b796ef36-39af-4461-bde1-59698c13cbc0
-- statement:
--   So we only have to prove that $(a + b + c)^2\geq a + b + c + ab + bc + ca \iff a^2 + b^2 + c^2 + ab + bc + ca\geq a + b + c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32820 (a b c : ℝ) : (a + b + c) ^ 2 ≥ a + b + c + a * b + b * c + c * a ↔ a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ a + b + c   :=  by sorry
