-- Prove2me | Theorems.Thm_lean_workbook_plus_33783
-- name    : lean_workbook_plus_33783
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/2067def7-9af7-4169-8169-c780911db7d5
-- statement:
--   Prove that $f(x) = x^2$ is continuous at $x = 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33783 : ContinuousAt (fun x : ℝ => x^2) 3   :=  by sorry
