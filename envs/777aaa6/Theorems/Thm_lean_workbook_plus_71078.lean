-- Prove2me | Theorems.Thm_lean_workbook_plus_71078
-- name    : lean_workbook_plus_71078
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d22585c9-4e0b-4875-9f59-8d1f5367afd6
-- statement:
--   I don't understand. If all coefficients of $P(x)$ are non-positive, then $P(x) \leq 0$ for $x \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71078 (P : Polynomial ℝ) (hP : ∀ n, P.coeff n ≤ 0) (x : ℝ) (hx : 0 ≤ x) : P.eval x ≤ 0   :=  by sorry
