-- Prove2me | Theorems.Thm_lean_workbook_plus_23158
-- name    : lean_workbook_plus_23158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/df685cd6-556d-4a84-890e-c539dc986bf2
-- statement:
--   Prove that $f(x)=x$ for all $x<0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23158 (f : ℝ → ℝ) (hf: f = fun x => if x < 0 then x else f x) : ∀ x < 0, f x = x   :=  by sorry
