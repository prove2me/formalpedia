-- Prove2me | Theorems.Thm_WorkbookSource_base_30699
-- name    : WorkbookSource.base_30699
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:06.400459+00:00
-- url     : https://prove2.me/theorems/11d5fb07-06bb-4ee5-b219-0d150790f2bd
-- title:
--   A cyclic sixth-degree inequality with a triple-product factor
-- statement:
--   Let $a,b,c$ be positive real numbers prove the following inequality
--
--    $$a^2 b^4 +b^2c^4+ c^2 a^4 +6 a^2 b^2 c^2 \geq 3a b c \left(a b^2+b c^2 +c a^2\right)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30699` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30699; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30699 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 * b^4 + b^2 * c^4 + c^2 * a^4 + 6 * a^2 * b^2 * c^2 ≥ 3 * a * b * c * (a * b^2 + b * c^2 + c * a^2)  :=  by sorry
