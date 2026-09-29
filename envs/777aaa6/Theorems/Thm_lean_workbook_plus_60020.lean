-- Prove2me | Theorems.Thm_lean_workbook_plus_60020
-- name    : lean_workbook_plus_60020
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/88dd0685-73c6-4978-80f2-8b722dd7f38a
-- statement:
--   Find all function $ f:R->R $ for which satisfy $ f(1)=1 $ and $ f(x+y)=3^y f(x) + 2^x f(y) $ for each $x,y$ element of $ R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60020 (f : ℝ → ℝ) (h₁ : f 1 = 1) (h₂ : ∀ x y : ℝ, f (x + y) = 3 ^ y * f x + 2 ^ x * f y) : ∀ x : ℝ, f x = 1   :=  by sorry
