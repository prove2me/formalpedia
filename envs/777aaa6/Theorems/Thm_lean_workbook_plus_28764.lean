-- Prove2me | Theorems.Thm_lean_workbook_plus_28764
-- name    : lean_workbook_plus_28764
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/0476cef3-837d-4c85-97f7-f5118bae6a6d
-- statement:
--   Indeed, $x_1^2+x_2^2+\cdots+x_n^2=0$ implies $x_1=x_2=\cdots=x_n=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28764 (n : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 0) :
  ∀ i, x i = 0   :=  by sorry
