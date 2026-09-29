-- Prove2me | Theorems.Thm_lean_workbook_plus_14274
-- name    : lean_workbook_plus_14274
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/728d0f64-eb30-423c-bd83-f87bc657e858
-- statement:
--   Prove that $4\sum a^{3}b^{2}=4.\sum \frac{a^{2}b^{2}}{bc}\geq 4.\sum(ab+bc+ca)$, given $a, b, c$ are positive reals and $abc=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14274 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : 4 * (a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2) ≥ 4 * (a * b + b * c + c * a)   :=  by sorry
