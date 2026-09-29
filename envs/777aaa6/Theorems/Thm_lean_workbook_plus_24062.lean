-- Prove2me | Theorems.Thm_lean_workbook_plus_24062
-- name    : lean_workbook_plus_24062
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b39353c2-cef4-4327-a661-f97e051cd6b1
-- statement:
--   $f(x)=x^2+a$ $\forall x$ and so $f(\mathbb R)=[a,+\infty)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24062 (a : ℝ) : Set.range (fun x : ℝ => x^2 + a) = Set.Ici a   :=  by sorry
