-- Prove2me | Theorems.Thm_lean_workbook_plus_16739
-- name    : lean_workbook_plus_16739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/77cf0a86-221a-4f4e-b736-9f88a88d3425
-- statement:
--   Follow schur: $ r \ge\ \frac {p(4q - p^2)}{9} \rightarrow q \le\ \frac {p^3 + 36}{4p + 9}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16739 (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hpq : p + q + r = 1) (hpqr : p * q * r = 1) (h : r ≥ p * (4 * q - p ^ 2) / 9) : q ≤ p ^ 3 + 36 / (4 * p + 9)   :=  by sorry
