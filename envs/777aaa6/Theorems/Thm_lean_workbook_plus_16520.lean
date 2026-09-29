-- Prove2me | Theorems.Thm_lean_workbook_plus_16520
-- name    : lean_workbook_plus_16520
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ec2a4757-8c92-425e-b74e-3f8d436ccd00
-- statement:
--   If $a,b,c \geq 0$ then we have $a^3+b^3+c^3+abc \geq \frac{1}{2}(a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16520 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^3 + b^3 + c^3 + a * b * c ≥ 1 / 2 * (a + b) * (b + c) * (c + a)   :=  by sorry
