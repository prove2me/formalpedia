-- Prove2me | Theorems.Thm_lean_workbook_plus_9471
-- name    : lean_workbook_plus_9471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a38d5399-b73d-4e31-8fb8-02f5d221953e
-- statement:
--   Prove that $4(a^2-ab+b^2) \ge (a+b)^2$ for positive reals $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9471 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 4 * (a^2 - a * b + b^2) ≥ (a + b)^2   :=  by sorry
