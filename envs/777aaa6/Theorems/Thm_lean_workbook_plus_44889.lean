-- Prove2me | Theorems.Thm_lean_workbook_plus_44889
-- name    : lean_workbook_plus_44889
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ab70062b-eac7-402c-8191-b916c3fa6ef8
-- statement:
--   What is the effect of multiplying the function $f(x)$ by a constant $k$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44889 (f : ℝ → ℝ) (k : ℝ) : (fun x => k * f x) = k • f   :=  by sorry
