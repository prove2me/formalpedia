-- Prove2me | Theorems.Thm_lean_workbook_plus_11742
-- name    : lean_workbook_plus_11742
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3bd8e619-e0a8-4437-a64e-263ee1f3b35f
-- statement:
--   We want $\frac{[ACE]}{[ABCDEF]}=.7$ so \n \begin{align*} \frac{(r+1)^2-(r+1)+1}{(r+2)^2-3} &= .7 \ (r+1)^2-(r+1)+1 &= .7(r+2)^2-2.1 \ r^2+r+1 &= .7r^2+2.8r+.7 \ .3r^2-1.8r+.3 &= 0 \ r^2-6r+1 &= 0. \end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11742  (r : ℝ)
  (h₀ : (r + 1)^2 - (r + 1) + 1 = 0.7 * ((r + 2)^2 - 3)) :
  r^2 - 6 * r + 1 = 0   :=  by sorry
