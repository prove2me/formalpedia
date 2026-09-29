-- Prove2me | Theorems.Thm_lean_workbook_plus_71508
-- name    : lean_workbook_plus_71508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/71915fb4-fc04-498f-8f3b-1da3276198de
-- statement:
--   $P(x,-2x)$ $\implies$ $f(x)f(-x)=1-xf(-x)+x$ \n$P(-x,2x)$ $\implies$ $f(x)f(-x)=1+xf(x)-x$ \nSubtracting, we get $f(-x)=2-f(x)$ $\forall x\ne 0$ , still true when $x=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71508  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : x ≠ 0)
  (h₁ : 2 * f x * f (-x) = 2 - x * f (-x) + x)
  (h₂ : 2 * f x * f (-x) = 2 + x * f x - x) :
  f (-x) = 2 - f x   :=  by sorry
