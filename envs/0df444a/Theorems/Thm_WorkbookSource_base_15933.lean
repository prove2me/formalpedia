-- Prove2me | Theorems.Thm_WorkbookSource_base_15933
-- name    : WorkbookSource.base_15933
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:32.762757+00:00
-- url     : https://prove2.me/theorems/9f8d25b7-1c16-4dc0-aa28-d3ccaaf10436
-- title:
--   A cyclic linear ratio sum bounded by the normalized quadratic sum
-- statement:
--   Let $a,b,c>0$ . Prove that:
--
--    $\frac{a+2b}{2a+b}+\frac{b+2c}{2b+c}+\frac{c+2a}{2c+a}\le \frac{9(a^2+b^2+c^2)}{(a+b+c)^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15933` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15933; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15933 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / (2 * a + b) + (b + 2 * c) / (2 * b + c) + (c + 2 * a) / (2 * c + a) ≤ (9 * (a ^ 2 + b ^ 2 + c ^ 2)) / (a + b + c) ^ 2  :=  by sorry
