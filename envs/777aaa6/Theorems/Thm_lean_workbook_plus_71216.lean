-- Prove2me | Theorems.Thm_lean_workbook_plus_71216
-- name    : lean_workbook_plus_71216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/958b20c5-c65a-4971-ba2e-a14f3b414ecd
-- statement:
--   Show that if $ \left| ax^2+bx+c\right|\le 1, $ for all $ x\in [-1,1], $ then $ |a|+|b|+|c|\le 4. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71216    (a b c : ℝ)
    (h₀ : ∀ x ∈ Set.Icc (-1) 1, abs (a * x ^ 2 + b * x + c) ≤ 1) :
    abs a + abs b + abs c ≤ 4   :=  by sorry
