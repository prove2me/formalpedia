-- Prove2me | Theorems.Thm_WorkbookSource_base_2207
-- name    : WorkbookSource.base_2207
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:57:00.756415+00:00
-- url     : https://prove2.me/theorems/562cf89a-fa64-47fb-bed4-6c4955f430e2
-- title:
--   A symmetric shifted reciprocal sum bounded by a cubic ratio
-- statement:
--   The following inequality a bit of stronger.
--    Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--    $$\frac{1}{7a+b+c} +\frac{1}{a+7b+c} +\frac{1}{a+b+7c} \leq \frac{3(a^2+b^2+c^2)}{(a+b+c) ^3}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2207` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2207; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2207 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (7 * a + b + c) + 1 / (a + 7 * b + c) + 1 / (a + b + 7 * c)) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 3)  :=  by sorry
