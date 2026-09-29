-- Prove2me | Theorems.Thm_lean_workbook_plus_52843
-- name    : lean_workbook_plus_52843
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/dee097e5-5b67-4ecc-8172-4cac85f42f01
-- statement:
--   It is also equivalent to the following: \n \n $ \left(\frac {1}{b} + \frac {1}{c} + \frac {1}{a}\right)\left(\frac {(a - b)^2}{b} + \frac {(b - c)^2}{c} + \frac {(c - a)^2}{a}\right)$ $ \ge \left(\frac {a - b}{b} + \frac {b - c}{c} + \frac {c - a}{a}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52843 :
  ∀ a b c : ℝ, (1 / b + 1 / c + 1 / a) * ((a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - a) ^ 2 / a) ≥ ((a - b) / b + (b - c) / c + (c - a) / a) ^ 2   :=  by sorry
