-- Prove2me | Theorems.Thm_lean_workbook_plus_49172
-- name    : lean_workbook_plus_49172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6d50f6d2-de3c-4f7b-9458-bdd87f3b6c5c
-- statement:
--   Let $a,b,c \in \mathbb{R}$ such that $a^3b+b^3c+c^3a = \frac23(a^2b^2+b^2c^2+c^2a^2)$ . Prove that $(a^2+b^2+c^2)^2 \geq 4(a^3b+b^3c+c^3a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49172 (a b c : ℝ) (h : a ^ 3 * b + b ^ 3 * c + c ^ 3 * a = 2 / 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 4 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)   :=  by sorry
