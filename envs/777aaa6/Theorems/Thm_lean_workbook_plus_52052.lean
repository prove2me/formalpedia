-- Prove2me | Theorems.Thm_lean_workbook_plus_52052
-- name    : lean_workbook_plus_52052
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/81ce8bf9-1fb1-4add-8538-0b16bc688658
-- statement:
--   Find $ p(p - 1)(p - 8) + q(q - 1)(q - 8) + r(r - 1)(r - 8)$ given the equation $ x^3 - 9x^2 + 8x + 2 = 0$ with roots $ p$ , $ q$ , $ r$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52052 (p q r : ℂ) (hp : p^3 - 9 * p^2 + 8 * p + 2 = 0) (hq : q^3 - 9 * q^2 + 8 * q + 2 = 0) (hr : r^3 - 9 * r^2 + 8 * r + 2 = 0) : p * (p - 1) * (p - 8) + q * (q - 1) * (q - 8) + r * (r - 1) * (r - 8) = -6   :=  by sorry
