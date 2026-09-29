-- Prove2me | Theorems.Thm_lean_workbook_plus_13378
-- name    : lean_workbook_plus_13378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b8bbe512-ee5c-4b5e-9a20-126ebc1c8195
-- statement:
--   bc + ca + ab + 1 > 0 for the case when the numbers a, b, c are all $\leq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13378 (a b c : ℝ) (ha : a ≤ 0) (hb : b ≤ 0) (hc : c ≤ 0) : (b * c + c * a + a * b + 1) > 0   :=  by sorry
