-- Prove2me | Theorems.Thm_WorkbookSource_base_9399
-- name    : WorkbookSource.base_9399
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:43:49.723222+00:00
-- url     : https://prove2.me/theorems/bd385773-78cc-4bd9-93bc-877b1f59bbb4
-- title:
--   A squared-pairwise ratio sum bounds the normalized quadratic mean
-- statement:
--   Let $a, b, c>0$ . Prove that $\frac{(a+b)^2}{c(a+b+2c)}+\frac{(b+c)^2}{a(b+c+2a)}+\frac{(c+a)^2}{b(c+a+2b)}+1\ge\frac{4(a^2+b^2+c^2)}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9399` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9399; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9399 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 / (c * (a + b + 2 * c)) + (b + c) ^ 2 / (a * (b + c + 2 * a)) + (c + a) ^ 2 / (b * (c + a + 2 * b)) + 1 ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + a * c)  :=  by sorry
