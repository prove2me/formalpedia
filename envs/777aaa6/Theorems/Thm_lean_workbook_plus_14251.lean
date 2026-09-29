-- Prove2me | Theorems.Thm_lean_workbook_plus_14251
-- name    : lean_workbook_plus_14251
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/705f85de-8c91-492e-a6ac-0c118cd0eb19
-- statement:
--   For $a,b,c \in \mathbb{R}$ so that $a+b+c=1$ Prove that $ab(3a-1)+ac(3b-1)+bc(3c-1) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14251 : ∀ a b c : ℝ, a + b + c = 1 → a * b * (3 * a - 1) + a * c * (3 * b - 1) + b * c * (3 * c - 1) ≥ 0   :=  by sorry
