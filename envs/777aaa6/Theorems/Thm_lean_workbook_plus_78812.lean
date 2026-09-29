-- Prove2me | Theorems.Thm_lean_workbook_plus_78812
-- name    : lean_workbook_plus_78812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/224ac56e-9b82-456e-97d3-d190d4910101
-- statement:
--   If $a, b, c>0, a^2+b^2+c^2=1, k, n\in\mathbb{N}, k\geq3n$ prove that $\frac{ka^2+(k-n)bc+n}{nb^2+(k-n)bc+nc^2}+\frac{kb^2+(k-n)ca+n}{nc^2+(k-n)ca+na^2}+\frac{kc^2+(k-n)ab+n}{na^2+(k-n)ab+nb^2}\geq6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78812 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) (k n : ℕ) (hk : k ≥ 3 * n) : (k * a^2 + (k - n) * b * c + n) / (n * b^2 + (k - n) * b * c + n * c^2) + (k * b^2 + (k - n) * c * a + n) / (n * c^2 + (k - n) * c * a + n * a^2) + (k * c^2 + (k - n) * a * b + n) / (n * a^2 + (k - n) * a * b + n * b^2) ≥ 6   :=  by sorry
