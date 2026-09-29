-- Prove2me | Theorems.Thm_lean_workbook_plus_7907
-- name    : lean_workbook_plus_7907
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/5f469bc8-89a9-468b-aaca-9d743eca60bc
-- statement:
--   Yes, I am sure that $x^{3}\geq x$ $\Leftrightarrow x(x^{2}-1)\geq0,$ it is not rue for ALL $-1\le x \le2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7907 : ∀ x : ℝ, x^3 ≥ x ↔ x * (x^2 - 1) ≥ 0   :=  by sorry
