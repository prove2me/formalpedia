-- Prove2me | Theorems.Thm_lean_workbook_plus_13017
-- name    : lean_workbook_plus_13017
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/1df1b855-cca2-4623-a667-a75731b780bd
-- statement:
--   If we're in the bad case, we can pick new variables $u=\tfrac{1}{x}, v=\tfrac{1}{y}, w=\tfrac{1}{z}$ (in 'good' cyclic order) and substitute into the original proposition to find: $\sum_\text{cyc} \frac{ (v+u)^2 v^2 }{ (v+u)^2 } \le 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13017 (x y z : ℝ) (hx : x ∈ Set.Ioi 0) (hy : y ∈ Set.Ioi 0) (hz : z ∈ Set.Ioi 0) (h : x * y * z = 1) :
  x ^ 2 / (x ^ 2 + y ^ 2) + y ^ 2 / (y ^ 2 + z ^ 2) + z ^ 2 / (z ^ 2 + x ^ 2) ≤ 3   :=  by sorry
