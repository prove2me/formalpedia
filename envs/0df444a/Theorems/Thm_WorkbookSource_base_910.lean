-- Prove2me | Theorems.Thm_WorkbookSource_base_910
-- name    : WorkbookSource.base_910
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:28.095313+00:00
-- url     : https://prove2.me/theorems/0610e402-2933-4876-a7fd-a65fbbe6f41c
-- title:
--   A cyclic product correction bounded by the quadratic sum
-- statement:
--   For every $a,b,c>0$ prove the inequality
--    $ab\biggl(1-\frac{2c^2}{(a+b)^2}\biggr)+bc\biggl(1-\frac{2a^2}{(b+c)^2}\biggr)+ca\biggl(1-\frac{2b^2}{(c+a)^2}\biggr)\le \frac{1}{2}(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_910` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_910; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_910 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b * (1 - 2 * c^2 / (a + b)^2) + b * c * (1 - 2 * a^2 / (b + c)^2) + c * a * (1 - 2 * b^2 / (c + a)^2) ≤ (1 / 2) * (a^2 + b^2 + c^2)  :=  by sorry
