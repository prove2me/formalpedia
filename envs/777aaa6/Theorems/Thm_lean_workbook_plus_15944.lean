-- Prove2me | Theorems.Thm_lean_workbook_plus_15944
-- name    : lean_workbook_plus_15944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/fba098b7-71cf-47bd-a90e-d1e1e61f4982
-- statement:
--   a=1+\epsilon, b=1+\epsilon, c=2 are triangle sides and satisfy 3a \ge b+c but give nearly the same result (for small \(\epsilon\))
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15944 (ε : ℝ) (hε : 0 < ε) (a b c : ℝ) (hab : a = 1 + ε) (hbc : b = 1 + ε) (hca : c = 2) (h : a + b > c) : 3 * a ≥ b + c   :=  by sorry
