-- Prove2me | Theorems.Thm_lean_workbook_plus_64302
-- name    : lean_workbook_plus_64302
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/333a54d9-4afa-444a-81cf-7850112ebe0d
-- statement:
--   let $P(x,y)$ be the assersion, $$f(x+y)=x+f(y).$$ Then, $P(x,0)$ yields, $f(x)=x+f(0)=x+2.$ for all real numbers $x.$ \nTherefore, $f(1998)=1998+2=2000.$ Which corresponds to answer choice $\textbf{(E)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64302  (f : ℝ → ℝ)
  (h₀ : ∀ x, ∀ y, f (x + y) = x + f y)
  (h₁ : f 0 = 2) :
  f 1998 = 2000   :=  by sorry
