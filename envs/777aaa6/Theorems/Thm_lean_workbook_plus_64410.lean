-- Prove2me | Theorems.Thm_lean_workbook_plus_64410
-- name    : lean_workbook_plus_64410
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d4dafa18-31ab-48d2-a881-e64a98451801
-- statement:
--   If $a,b,c$ are non-negative numbers, no two of which are zero, then\n\n $\frac{a^{2}}{a+b}+\frac{b^{2}}{b+c}+\frac{c^{2}}{c+a}\leq \frac{3(a^{2}+b^{2}+c^{2})}{2(a+b+c)}$ .\n\n $\Longleftrightarrow \sum{a^{3}b^{2}}+\sum{a^{2}b^{3}}\leq \sum{a^{4}b}+\sum{ab^{4}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64410 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (hca : a + c ≠ 0) : (a^2 / (a + b) + b^2 / (b + c) + c^2 / (c + a) ≤ (3 * (a^2 + b^2 + c^2)) / (2 * (a + b + c))) ↔ (a^3 * b^2 + b^3 * c^2 + c^3 * a^2 + a^2 * b^3 + b^2 * c^3 + c^2 * a^3 ≤ a^4 * b + b^4 * c + c^4 * a + a * b^4 + b * c^4 + c * a^4)   :=  by sorry
