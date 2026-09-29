-- Prove2me | Theorems.Thm_lean_workbook_plus_50431
-- name    : lean_workbook_plus_50431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/233f9ddd-fff0-4771-96bb-348dc4b8c4ed
-- statement:
--   Let $a,b,c,d\geq 0$ ,prove that: $b^3+c^3+d^3+a^3 \geq \frac{1}{2}(a+b+c+d)(ac+bd).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50431 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : a^3 + b^3 + c^3 + d^3 ≥ 1 / 2 * (a + b + c + d) * (a * c + b * d)   :=  by sorry
