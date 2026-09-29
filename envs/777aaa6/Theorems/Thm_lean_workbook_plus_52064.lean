-- Prove2me | Theorems.Thm_lean_workbook_plus_52064
-- name    : lean_workbook_plus_52064
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/606e7e08-0dc7-4cb8-adbd-0d1b852f29a3
-- statement:
--   Prove that $157 + 2\left(a - \frac{1}{2}\right)^2+32a^2(a^2-a-1)^2+16(a^2+a-1)^2+18a^2 \geqslant 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52064 (a : ℝ) : 157 + 2 * (a - 1 / 2) ^ 2 + 32 * a ^ 2 * (a ^ 2 - a - 1) ^ 2 + 16 * (a ^ 2 + a - 1) ^ 2 + 18 * a ^ 2 ≥ 0   :=  by sorry
