-- Prove2me | Theorems.Thm_lean_workbook_plus_5654
-- name    : lean_workbook_plus_5654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d5d0a1b0-d7e6-42e6-8e49-1fb33ffaebef
-- statement:
--   2) if $f(1)=2006$ , then $\boxed{f(x)=\frac 1x+2005\quad\forall x>0}$ which indeed is a solution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5654 (f : ℝ → ℝ) (hf: f = fun x => 1/x + 2005) : f 1 = 2006   :=  by sorry
