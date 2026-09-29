-- Prove2me | Theorems.Thm_lean_workbook_plus_23099
-- name    : lean_workbook_plus_23099
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4867ce52-4c79-4021-9e56-f7904c5aca33
-- statement:
--   Prove if the function $f(x)=x^2+\sin(x)$ is surjective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23099 : ∀ y : ℝ, ∃ x : ℝ, x^2 + sin x = y   :=  by sorry
