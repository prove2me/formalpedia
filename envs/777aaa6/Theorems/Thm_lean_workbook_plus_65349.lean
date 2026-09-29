-- Prove2me | Theorems.Thm_lean_workbook_plus_65349
-- name    : lean_workbook_plus_65349
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/64df18c2-eb13-4f9d-8faf-ada2978a77d0
-- statement:
--   An alternative approach is to use the formula $D = ST$ (distance = speed * time). Let $t$ be the time on the highway route and $D$ be the highway distance. We can write the equations as $D = 45t$ and $(D-3) = 36(t - \frac{1}{20})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65349 (D t : ℝ) (h₁ : D = 45 * t) (h₂ : D - 3 = 36 * (t - 1/20)) : t = 3/4 ∧ D = 33/4   :=  by sorry
