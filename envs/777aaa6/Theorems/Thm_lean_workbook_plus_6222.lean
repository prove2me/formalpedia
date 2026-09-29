-- Prove2me | Theorems.Thm_lean_workbook_plus_6222
-- name    : lean_workbook_plus_6222
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/7ebc936c-8482-4f50-8862-aae6e6212a53
-- statement:
--   Let $a $ , $b $ , and $c $ be non-negative reals. Prove that $a^3+b^3+c^3+6abc\ge \frac{(a+b+c)^3}{4} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6222 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^3 + b^3 + c^3 + 6 * a * b * c ≥ (a + b + c)^3 / 4   :=  by sorry
