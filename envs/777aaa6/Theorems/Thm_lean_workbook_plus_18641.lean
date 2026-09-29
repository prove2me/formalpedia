-- Prove2me | Theorems.Thm_lean_workbook_plus_18641
-- name    : lean_workbook_plus_18641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0f37aab9-000b-439a-9010-d43b5dec162c
-- statement:
--   Let $a,b,c>0$ and $a^3+b^3+c^3=a^2+b^2+c^2$ . Prove $ \frac{1}{\sqrt{a^2-ab+b^2}}+ \frac{1}{\sqrt{b^2-bc+c^2}}+ \frac{1}{\sqrt{c^2-ca+a^2}}\ge \frac{3}{2}\sqrt{\frac{(a+b)(b+c)(c+a)}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18641 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) (habc : a + b + c = 1) (h : a^3 + b^3 + c^3 = a^2 + b^2 + c^2) : (1 / Real.sqrt (a^2 - a * b + b^2) + 1 / Real.sqrt (b^2 - b * c + c^2) + 1 / Real.sqrt (c^2 - c * a + a^2)) ≥ 3 / 2 * Real.sqrt ((a + b) * (b + c) * (c + a) / 2)   :=  by sorry
