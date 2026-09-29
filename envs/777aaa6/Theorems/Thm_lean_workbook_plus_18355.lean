-- Prove2me | Theorems.Thm_lean_workbook_plus_18355
-- name    : lean_workbook_plus_18355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/370465bd-f049-4b66-a75f-55a5e6b1a522
-- statement:
--   $f(x)=\frac1x, g(x)=-\frac1x$ , that was easy
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18355 (x : ℝ) (f g : ℝ → ℝ) (hf : f x = 1 / x) (hg : g x = -1 / x) : f x + g x = 0   :=  by sorry
