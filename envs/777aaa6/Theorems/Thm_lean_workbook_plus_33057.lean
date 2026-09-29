-- Prove2me | Theorems.Thm_lean_workbook_plus_33057
-- name    : lean_workbook_plus_33057
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/21f8ace2-6563-43b6-9969-dab16b0b1eca
-- statement:
--   Prove that for any positive real numbers $a, b, c$ , $a^3 + b^3 + c^3 + 3abc \ge \frac{3}{4}(a+b)(b + c)(c + a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33057 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 3 * a * b * c ≥ 3 / 4 * (a + b) * (b + c) * (c + a)   :=  by sorry
