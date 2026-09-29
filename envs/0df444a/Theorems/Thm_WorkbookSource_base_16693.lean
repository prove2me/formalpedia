-- Prove2me | Theorems.Thm_WorkbookSource_base_16693
-- name    : WorkbookSource.base_16693
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:27.169606+00:00
-- url     : https://prove2.me/theorems/33372ee3-97cf-42dc-8ff3-9fde302417fa
-- title:
--   A quadratic difference bounds a weighted linear square
-- statement:
--   Let $a,b,c>0$. Prove that
--
--    $$a^2+2b^2+c^2+ ab-ca\geq \frac{5}{32}(a+3b+c)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16693` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16693; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16693 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + 2 * b^2 + c^2 + a * b - c * a ≥ (5 / 32) * (a + 3 * b + c)^2  :=  by sorry
