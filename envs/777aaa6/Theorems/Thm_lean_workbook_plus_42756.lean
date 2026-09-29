-- Prove2me | Theorems.Thm_lean_workbook_plus_42756
-- name    : lean_workbook_plus_42756
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/16574270-a161-43a0-8913-85dc03b1b541
-- statement:
--   $=> f(0)+f(x)=2f(0)+x =>f(x)=x+f(0), \forall x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42756 (f : ℝ → ℝ) (hf: f 0 + f x = 2 * f 0 + x) : f x = x + f 0   :=  by sorry
