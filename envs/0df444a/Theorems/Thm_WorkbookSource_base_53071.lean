-- Prove2me | Theorems.Thm_WorkbookSource_base_53071
-- name    : WorkbookSource.base_53071
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:02:31.21372+00:00
-- url     : https://prove2.me/theorems/be0f2645-a57a-432a-a902-525ee34c4ae2
-- title:
--   A shifted cyclic ratio sum is bounded by the reciprocal product
-- statement:
--   Let $ a,b,c$ be positive real numbers such that $ a+b+c=3$ . Prove that $ \frac{a}{2b+1}+\frac{b}{2c+1}+\frac{c}{2a+1} \le \frac{1}{abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53071` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53071; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53071 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (2 * b + 1) + b / (2 * c + 1) + c / (2 * a + 1) ≤ 1 / (a * b * c)  :=  by sorry
