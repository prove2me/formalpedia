-- Prove2me | Theorems.Thm_lean_workbook_plus_63464
-- name    : lean_workbook_plus_63464
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8913798b-e113-4189-a8ab-221363596cce
-- statement:
--   Equivalent to.. $c^2-(a+b)c+\frac {(a+b)^2}{4}\geq 0$ which is obvious since $(c-\frac {a+b}{2})^2\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63464 (a b c : ℝ) : (c^2 - (a + b) * c + (a + b)^2 / 4) ≥ 0   :=  by sorry
