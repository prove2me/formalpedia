-- Prove2me | Theorems.Thm_lean_workbook_plus_16402
-- name    : lean_workbook_plus_16402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/20d6cc3c-be35-421a-a69b-6ffc4bc0f41c
-- statement:
--   If $a_n \ge \frac{1}{2^n},$ then $a_n ^{1-1/n} \le 2 a_n.$ If $a_n < \frac{1}{2^n},$ then $a_n ^{1-1/n} < 2a_n + \frac{1}{2^{n-1}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16402 (a n : ℕ) : (a : ℝ) ≥ 1 / 2 ^ n → (a : ℝ) ^ (1 - 1 / n) ≤ 2 * a ∧ (a : ℝ) < 1 / 2 ^ n → (a : ℝ) ^ (1 - 1 / n) < 2 * a + 1 / 2 ^ (n - 1)   :=  by sorry
