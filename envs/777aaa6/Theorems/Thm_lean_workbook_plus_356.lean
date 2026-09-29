-- Prove2me | Theorems.Thm_lean_workbook_plus_356
-- name    : lean_workbook_plus_356
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/59e17774-b5fc-4e0d-9eb6-241784031f9f
-- statement:
--   $n=2\implies a={9-2n\over 6n}={5\over 12}\implies x=n+a={29\over 12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_356  (n x a : ℝ)
  (h₀ : n = 2)
  (h₁ : a = (9 - 2 * n) / (6 * n))
  (h₂ : x = n + a) :
  x = 29 / 12   :=  by sorry
