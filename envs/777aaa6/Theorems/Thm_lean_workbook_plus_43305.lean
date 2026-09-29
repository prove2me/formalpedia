-- Prove2me | Theorems.Thm_lean_workbook_plus_43305
-- name    : lean_workbook_plus_43305
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/aa3644d6-b6a0-4a68-a495-c86e0ed2888f
-- statement:
--   If $T=0$ , we get $\boxed{\text{S2 : }f(x)=c\quad\forall x}$ which indeed fits, whatever is $c\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43305 (f : ℝ → ℝ) (c : ℝ) (hf: f = fun x ↦ c) : f x = c   :=  by sorry
