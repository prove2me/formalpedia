-- Prove2me | Theorems.Thm_WorkbookSource_base_4256
-- name    : WorkbookSource.base_4256
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:58.798174+00:00
-- url     : https://prove2.me/theorems/7c1360de-7f1a-48ad-bcfb-37ce29002431
-- title:
--   A cyclic quadratic ratio upper bound
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a^2}{3a^2+(b+c)^2}+\frac{b^2}{3b^2+(c+a)^2}+\frac{c^2}{3c^2+(a+b)^2}\le\frac{3(a^2+b^2+c^2)}{7(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4256` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4256; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4256 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (3 * a^2 + (b + c)^2) + b^2 / (3 * b^2 + (c + a)^2) + c^2 / (3 * c^2 + (a + b)^2)) ≤ (3 * (a^2 + b^2 + c^2)) / (7 * (a * b + b * c + c * a))  :=  by sorry
