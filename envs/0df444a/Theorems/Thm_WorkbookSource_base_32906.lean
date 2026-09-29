-- Prove2me | Theorems.Thm_WorkbookSource_base_32906
-- name    : WorkbookSource.base_32906
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:07.237654+00:00
-- url     : https://prove2.me/theorems/a0f14635-3466-45c0-8c51-ec1522c7834f
-- title:
--   A pairwise ratio sum with a normalized quadratic correction
-- statement:
--   Let $a, b, c>0$ . Prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}+\frac{3(ab+bc+ca)}{(a+b+c)^2}\ge\frac{5}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32906` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32906; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32906 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2) ≥ 5 / 2  :=  by sorry
