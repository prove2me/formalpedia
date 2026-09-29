-- Prove2me | Theorems.Thm_lean_workbook_plus_47039
-- name    : lean_workbook_plus_47039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/40115358-c05b-4bce-a494-7748a645251e
-- statement:
--   $\frac{ab + ac + bc}{a^2 + b^2 + c^2} \leq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47039 (a b c : ℝ) : (a * b + a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1   :=  by sorry
