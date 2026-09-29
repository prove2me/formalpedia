-- Prove2me | Theorems.Thm_lean_workbook_plus_10900
-- name    : lean_workbook_plus_10900
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a7c114e3-522d-44ac-b20a-4c15a5d61383
-- statement:
--   Given $f(x)=\begin{cases}2x\text{ if }x<0.5\\2-2x\text{ if }x\geq 0.5\end{cases}$, does $f([0,1]) \subset [0,1]$ hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10900 (f : ℝ → ℝ) (f_of : ∀ x < 0.5, f x = 2 * x) (f_on : ∀ x ≥ 0.5, f x = 2 - 2 * x) : ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1   :=  by sorry
