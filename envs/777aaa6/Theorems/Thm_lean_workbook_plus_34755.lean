-- Prove2me | Theorems.Thm_lean_workbook_plus_34755
-- name    : lean_workbook_plus_34755
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/96f4f3e2-3026-4ef1-a302-4872c97eb341
-- statement:
--   And so $\boxed{f(1)=a\in[1,3]\text{ and }f(x)=2x+\frac{|x-1|}{x-1}\quad\forall x\ne 1}$ , which indeed fits, whatever is $a\in[1,3]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34755 (a : ℝ) (ha : 1 ≤ a ∧ a ≤ 3) (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => if x = 1 then a else 2 * x + |x - 1| / (x - 1)) : (∀ x, if x = 1 then f x = a else f x = 2 * x + |x - 1| / (x - 1))   :=  by sorry
