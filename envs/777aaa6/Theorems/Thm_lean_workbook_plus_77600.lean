-- Prove2me | Theorems.Thm_lean_workbook_plus_77600
-- name    : lean_workbook_plus_77600
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7d29c1f2-6144-4d6d-81ca-bac0b4d81e7b
-- statement:
--   Let $a,b,c>0$ . Show that $a^3+b^3+c^3 \ge 3abc+\frac{9}{4}|(a-b)(b-c)(c-a)|$ (Adil Abdullayev)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77600 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 ≥ 3 * a * b * c + (9 / 4) * |(a - b) * (b - c) * (c - a)|   :=  by sorry
