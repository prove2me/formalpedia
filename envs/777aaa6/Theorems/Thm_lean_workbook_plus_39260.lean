-- Prove2me | Theorems.Thm_lean_workbook_plus_39260
-- name    : lean_workbook_plus_39260
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f9624e2a-4726-4f53-8bfa-a99ec1660287
-- statement:
--   Let $a,b,c$ be real numbers such that $abc \neq 0$ and $a+b+c = 0$ . Prove that:\n\n$$\frac{1}{a^2+3b^2+3c^2}+\frac{1}{b^2+3c^2+3a^2}+\frac{1}{c^2+3a^2+3b^2} \geq \frac{4}{3(a^2+b^2+c^2)}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39260 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (habc : a + b + c = 0) : (1 / (a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2) + 1 / (b ^ 2 + 3 * c ^ 2 + 3 * a ^ 2) + 1 / (c ^ 2 + 3 * a ^ 2 + 3 * b ^ 2) ≥ 4 / (3 * (a ^ 2 + b ^ 2 + c ^ 2)))   :=  by sorry
