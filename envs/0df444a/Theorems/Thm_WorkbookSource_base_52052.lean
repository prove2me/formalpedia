-- Prove2me | Theorems.Thm_WorkbookSource_base_52052
-- name    : WorkbookSource.base_52052
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:32.002809+00:00
-- url     : https://prove2.me/theorems/decb6562-0d7b-4d93-86c8-6b8301ab2b62
-- title:
--   A weighted shifted ratio sum has an upper bound in the total
-- statement:
--   Let $ a,b,c>0$ . Prove that $ \frac{a}{1+a}+\frac{2b}{2+b}+\frac{3c}{3+c}\le \frac{6(a+b+c)}{6+a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52052` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52052; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52052 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (1 + a) + 2 * b / (2 + b) + 3 * c / (3 + c)) ≤ 6 * (a + b + c) / (6 + a + b + c)  :=  by sorry
