-- Prove2me | Theorems.Thm_lean_workbook_plus_49192
-- name    : lean_workbook_plus_49192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/1f43fcef-b89d-45ba-a80f-e517f6280440
-- statement:
--   Prove that if $x \geq 0$ and $y$ are real numbers for which $y^2 \geq x(x + 1)$, then $(y - 1)^2 \geq x(x-1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49192 (x y : ℝ) (hx: x ≥ 0) (hy: y^2 ≥ x * (x + 1)) : (y - 1)^2 ≥ x * (x - 1)   :=  by sorry
