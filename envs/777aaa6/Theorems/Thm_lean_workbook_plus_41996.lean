-- Prove2me | Theorems.Thm_lean_workbook_plus_41996
-- name    : lean_workbook_plus_41996
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f128dc8c-0b3e-4f11-a9b2-086d51a7bf29
-- statement:
--   Prove that $0 < \frac{a+d}{1+\frac{ad}{c^2}} < c$ given $c>0$, $0<a<c$, and $0<d<c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41996    (a d c : ℝ) (hc : 0 < c) (ha : 0 < a ∧ a < c) (hd : 0 < d ∧ d < c)
    (had : a * d < c^2) :
  0 < (a + d) / (1 + a * d / c^2) ∧ (a + d) / (1 + a * d / c^2) < c   :=  by sorry
