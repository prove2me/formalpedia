-- Prove2me | Theorems.Thm_lean_workbook_plus_35381
-- name    : lean_workbook_plus_35381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/63cd8006-f9f4-4efa-b7f8-eea104557889
-- statement:
--   Prove that $a^{2}+b^{2}+c^{2}-ab-bc-ca \geq 3(a-b)(b-c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35381 (a b c : ℝ) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ 3 * (a - b) * (b - c)   :=  by sorry
