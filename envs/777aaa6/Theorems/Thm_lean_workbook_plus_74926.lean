-- Prove2me | Theorems.Thm_lean_workbook_plus_74926
-- name    : lean_workbook_plus_74926
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9788693d-c27d-440b-917d-fec5d904793a
-- statement:
--   $8f(x)=2f(x) \Rightarrow f(x)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74926  (f : ℝ → ℝ)
  (h₀ : 8 * f x = 2 * f x) :
  f x = 0   :=  by sorry
