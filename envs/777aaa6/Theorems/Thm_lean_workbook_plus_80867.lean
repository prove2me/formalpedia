-- Prove2me | Theorems.Thm_lean_workbook_plus_80867
-- name    : lean_workbook_plus_80867
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/46d4db53-b6e9-4e65-941c-1f80907f99c0
-- statement:
--   $f\left(x\right)-f\left(y\right)=\left(ax^2+bx+c\right)-\left(ay^2+by+c\right)=\left(x-y\right)\left(a\left(x+y\right)+b\right)$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80867  (a b c x y : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^2 + b * x + c)
  (h₁ : x ≠ y) :
  f x - f y = (x - y) * (a * (x + y) + b)   :=  by sorry
