-- Prove2me | Theorems.Thm_lean_workbook_plus_52484
-- name    : lean_workbook_plus_52484
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8e639972-9d15-4e03-9494-d1a1b879e14d
-- statement:
--   Studying the function $ f:\left[-\frac{\pi}{2},\frac{\pi}{2}\right]\to\mathbb R$ , $ f(x) = sin^{2}(x)+cos(x)-\frac{5}{4}$ we get that $ f(x)\leq 0$ $ \forall x\in\left[-\frac{\pi}{2},\frac{\pi}{2}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52484 :
  ∀ x ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2), (Real.sin x)^2 + Real.cos x - 5 / 4 ≤ 0   :=  by sorry
