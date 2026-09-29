-- Prove2me | Theorems.Thm_lean_workbook_plus_63556
-- name    : lean_workbook_plus_63556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8dd5728a-5843-4684-8b24-b9fa2f5dc30e
-- statement:
--   Try to prove that the cubic $\frac{x^3}{3}+\frac{x^2}{2}+x$ is injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63556 (x y : ℝ) (h : x^3 / 3 + x^2 / 2 + x = y^3 / 3 + y^2 / 2 + y) : x = y   :=  by sorry
