-- Prove2me | Theorems.Thm_lean_workbook_plus_13306
-- name    : lean_workbook_plus_13306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/00e617a3-e0b5-4a6f-959c-8d4ee21952d2
-- statement:
--   The probability of not getting an event of probability p is 1-p. The probability of not getting it twice is $ (1-p)(1-p)=(1-p)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13306  (p : ℝ)
  (h₀ : 0 ≤ p ∧ p ≤ 1) :
  (1 - p) * (1 - p) = (1 - p)^2   :=  by sorry
