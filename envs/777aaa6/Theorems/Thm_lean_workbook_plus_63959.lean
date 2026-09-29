-- Prove2me | Theorems.Thm_lean_workbook_plus_63959
-- name    : lean_workbook_plus_63959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e54657f3-4683-4259-981b-5b545c7eaf2e
-- statement:
--   If $x^5 - x ^3 + x = a,$ prove that $x^6 \geq 2a - 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63959 (x a : ℝ) (h : x^5 - x^3 + x = a) : x^6 ≥ 2 * a - 1   :=  by sorry
