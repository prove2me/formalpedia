-- Prove2me | Theorems.Thm_lean_workbook_plus_20775
-- name    : lean_workbook_plus_20775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/de2ffca4-42a3-4218-bd30-b21c50f0a132
-- statement:
--   Let $a$ and $b$ be two positive real numbers with $a \le 2b \le 5a .$ Prove that $a^2+ b^2 \le \frac{29}{10} ab$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20775 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 2 * b) (h3 : 2 * b ≤ 5 * a) : a^2 + b^2 ≤ (29 / 10) * a * b   :=  by sorry
