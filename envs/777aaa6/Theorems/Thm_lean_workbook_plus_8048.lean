-- Prove2me | Theorems.Thm_lean_workbook_plus_8048
-- name    : lean_workbook_plus_8048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/068efd4c-62fc-44b2-8470-f77237359bf6
-- statement:
--   Finding the greatest value of $\sqrt{5 - x^2}$ is just like finding the maximum of $5 - x^2$ , and then square rooting that. Taking the derivative, we have $-2x = 0$ so $x = 0$ and the max is $5$ , thus the max of $\sqrt{5 - x^2}$ is $\boxed{\sqrt{5}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8048  (x : ℝ)
  (h₀ : 0 ≤ 5 - x^2) :
  Real.sqrt (5 - x^2) ≤ Real.sqrt 5   :=  by sorry
