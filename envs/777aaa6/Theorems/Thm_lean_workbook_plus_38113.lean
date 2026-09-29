-- Prove2me | Theorems.Thm_lean_workbook_plus_38113
-- name    : lean_workbook_plus_38113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/5e82a3ab-e9ec-4a93-ab56-983ebe014c1b
-- statement:
--   So for $x\ne 0$ , we have $f(x)=1$ and $f(0)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38113 (x : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x = 0 then 0 else 1) : f x = if x = 0 then 0 else 1   :=  by sorry
