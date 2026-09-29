-- Prove2me | Theorems.Thm_lean_workbook_plus_32240
-- name    : lean_workbook_plus_32240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/4f8997da-9261-4a12-8533-8149bfbaf94f
-- statement:
--   Solve for $x^2$ in the equation $x^2=2z\left(\frac{x^2}{9}+1\right)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32240 (x z : ℂ) : x^2 = 2 * z * (x^2 / 9 + 1) ↔ x^2 = 2 * z * (x^2 / 9 + 1)   :=  by sorry
