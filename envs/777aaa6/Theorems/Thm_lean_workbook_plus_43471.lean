-- Prove2me | Theorems.Thm_lean_workbook_plus_43471
-- name    : lean_workbook_plus_43471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c77c3c0b-925e-4f32-92cc-94c7f9b97342
-- statement:
--   Prove that if $a, b, c > 0$ and $\frac{1}{1+a} + \frac{1}{1+b} + \frac{1}{1+c} = 1$, then $abc \ge 8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43471 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 → a * b * c ≥ 8   :=  by sorry
