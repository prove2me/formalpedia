-- Prove2me | Theorems.Thm_lean_workbook_plus_72719
-- name    : lean_workbook_plus_72719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/480bf9a8-db68-4b55-9978-a75c061d0a0f
-- statement:
--   Find the value of $x$ so that the function $q(x)=\frac{1}{2}x-3$ has the given value $q(x)=-4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72719 (x : ℝ) (q : ℝ → ℝ) (h₁ : q = fun (x : ℝ) => 1 / 2 * x - 3) : q x = -4 ↔ x = -2   :=  by sorry
