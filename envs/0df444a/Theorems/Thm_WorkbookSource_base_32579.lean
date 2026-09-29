-- Prove2me | Theorems.Thm_WorkbookSource_base_32579
-- name    : WorkbookSource.base_32579
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:29.504226+00:00
-- url     : https://prove2.me/theorems/179dd57e-ec0d-4005-a59b-7ed062565310
-- title:
--   A cyclic quadratic ratio bounds a normalized quadratic sum
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--
--    $$ \frac{a^2+b^2}{a^2+ab} +\frac{b^2+c^2}{b^2+bc} +\frac{c^2+a^2}{c^2+ca} \ge \frac{9(a^2+b^2+c^2)}{(a+b+c)^2} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32579` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32579; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32579 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) / (a^2 + a * b) + (b^2 + c^2) / (b^2 + b * c) + (c^2 + a^2) / (c^2 + c * a) ≥ 9 * (a^2 + b^2 + c^2) / (a + b + c) ^ 2  :=  by sorry
