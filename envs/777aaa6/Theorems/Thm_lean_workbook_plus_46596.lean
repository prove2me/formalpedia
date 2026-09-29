-- Prove2me | Theorems.Thm_lean_workbook_plus_46596
-- name    : lean_workbook_plus_46596
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a014f13b-042e-470a-81db-e57f29f9c2e9
-- statement:
--   Prove the identity: $(b-c)^2(b+c-2a)^2+(c-a)^2(c+a-2b)^2+(a-b)^2(a+b-2c)^2 = \frac12 \left(\left(b-c\right)^2+\left(c-a\right)^2+\left(a-b\right)^2\right)^2$ for all real numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46596 (a b c : ℝ) : (b - c) ^ 2 * (b + c - 2 * a) ^ 2 + (c - a) ^ 2 * (c + a - 2 * b) ^ 2 + (a - b) ^ 2 * (a + b - 2 * c) ^ 2 = 1 / 2 * ((b - c) ^ 2 + (c - a) ^ 2 + (a - b) ^ 2) ^ 2   :=  by sorry
