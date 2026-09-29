-- Prove2me | Theorems.Thm_lean_workbook_plus_22356
-- name    : lean_workbook_plus_22356
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0b5ca871-0596-4e72-b444-47e16c14fe60
-- statement:
--   Prove that for any positive numbers $a$ and $b$, the following inequality holds:\n$\frac{a^3}{a^2+ab+b^2} \ge \frac{2a-b}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22356 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^3 / (a^2 + a * b + b^2) >= (2 * a - b) / 3)   :=  by sorry
