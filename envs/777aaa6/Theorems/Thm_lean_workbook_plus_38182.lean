-- Prove2me | Theorems.Thm_lean_workbook_plus_38182
-- name    : lean_workbook_plus_38182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3222a71b-ba86-4ca9-a43c-b2b7f2e9c4f5
-- statement:
--   Prove that if $f(x) = x^2$ for all $x \in \mathbb{R}$, then $f$ is continuous at $x = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38182 : ContinuousAt (fun x : ℝ => x^2) 0   :=  by sorry
