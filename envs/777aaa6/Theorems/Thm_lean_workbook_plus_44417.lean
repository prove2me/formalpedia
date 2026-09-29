-- Prove2me | Theorems.Thm_lean_workbook_plus_44417
-- name    : lean_workbook_plus_44417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ba6700aa-bfa7-4b3f-9883-2dc28ea30bc3
-- statement:
--   Prove that $(a + b + c)^2 \geq 3(bc + ca + ab)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44417 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (b * c + c * a + a * b)   :=  by sorry
