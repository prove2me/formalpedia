-- Prove2me | Theorems.Thm_lean_workbook_plus_19757
-- name    : lean_workbook_plus_19757
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b9de5b4c-0540-4e44-b6e3-aefabefd2992
-- statement:
--   Prove that the constant function $f(x)=a$ for all $x > 0$ is a solution to the functional equation $f(x+f(c))=f(x+c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19757 (a c : ℝ) (f : ℝ → ℝ) (hf: f = fun x => a) : f (x + f c) = f (x + c)   :=  by sorry
