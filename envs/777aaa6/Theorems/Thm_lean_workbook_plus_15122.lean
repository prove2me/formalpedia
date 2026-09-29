-- Prove2me | Theorems.Thm_lean_workbook_plus_15122
-- name    : lean_workbook_plus_15122
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6ecc486e-08b3-4742-9f57-48a22366d6f7
-- statement:
--   Given $ a, b, c > 0$ satisfy $ abc = 1$ . Prove that:\n$ \frac{1} {3a + 2b + c} + \frac {1} {3b + 2c + a} + \frac {1} {3c + 2a + b} \leq\ \frac {1} {2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (3 * a + 2 * b + c) + 1 / (3 * b + 2 * c + a) + 1 / (3 * c + 2 * a + b) ≤ 1 / 2   :=  by sorry
