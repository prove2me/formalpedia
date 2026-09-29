-- Prove2me | Theorems.Thm_lean_workbook_plus_23305
-- name    : lean_workbook_plus_23305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2bc17328-d5d0-42cd-84c0-4a4e59ac493e
-- statement:
--   $\implies x^2-z^2=xy$ (as $x\neq 0$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23305  (x y z : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : y = (x^2 - z^2) / x) :
  x^2 - z^2 = x * y   :=  by sorry
