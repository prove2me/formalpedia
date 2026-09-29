-- Prove2me | Theorems.Thm_lean_workbook_plus_3573
-- name    : lean_workbook_plus_3573
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/cc9e2ac4-ce79-40a9-8dce-3f95aa4da947
-- statement:
--   If $a=-1$ and $r=1, \displaystyle \sum^{\infty}_{n=0} \left(ar^n + 1\right)$ converges because $$\sum^{\infty}_{n=0} \left(ar^n + 1\right)= \sum^\infty_{n=0}\left( -1\cdot 1^n+1\right)=\sum^\infty_{n=0}(-1+1)=\sum^\infty_{n=0}0=0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3573  (a r : ℝ)
  (n : ℕ)
  (h₀ : a = -1)
  (h₁ : r = 1)
  (h₂ : n = 0)
  (h₃ : ∑' n : ℕ, (a * r^n + 1) = 0) :
  ∑' n : ℕ, (a * r^n + 1) = 0   :=  by sorry
