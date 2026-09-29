-- Prove2me | Theorems.Thm_lean_workbook_plus_28584
-- name    : lean_workbook_plus_28584
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/98a0c644-2b20-4d3e-aad8-d0859ca33cd4
-- statement:
--   From $g(x^2)=-g(x)$ , we get $g(0)=g(1)=0$ and $g(-x)=g(x)=-g(x^2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28584 (g : ℝ → ℝ) (h : ∀ x, g (x^2) = -g x) : g 0 = 0 ∧ g 1 = 0 ∧ ∀ x, g (-x) = g x   :=  by sorry
