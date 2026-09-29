-- Prove2me | Theorems.Thm_lean_workbook_plus_13642
-- name    : lean_workbook_plus_13642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d84ef898-cfc0-4d09-baf3-f9cac9094128
-- statement:
--   For $t \in [0,1), [t] = 0$ , so $f(t) = t -\frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13642 (f : ℝ → ℝ) (hf: f = fun (t : ℝ) => t - 1/2) : ∀ t ∈ Set.Ico (0 : ℝ) 1, f t = t - 1/2   :=  by sorry
