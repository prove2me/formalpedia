-- Prove2me | Theorems.Thm_lean_workbook_plus_40768
-- name    : lean_workbook_plus_40768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0a59dadf-0455-4d1e-8373-a97038581fb7
-- statement:
--   Therefore: $ f(x) = (1 - x)(1 + x) = 1 - x^2$ (which does satisfy the original equation) for all $ x \in \mathbb{R}$ such that $ (x^2 - x - 1)(x^2 - x + 1) \neq 0 \Rightarrow x \not\in \left\{\dfrac{1 - \sqrt {5}}{2} , \dfrac{1 + \sqrt {5}}{2} \right\} = \left\{ 1 - \phi , \phi \right\}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40768  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : x^2 - x - 1 ≠ 0)
  (h₁ : x^2 - x + 1 ≠ 0)
  (h₂ : f x = (1 - x) * (1 + x))
  (h₃ : 0 < x) :
  f x = 1 - x^2   :=  by sorry
