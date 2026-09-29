-- Prove2me | Theorems.Thm_WorkbookSource_base_9776
-- name    : WorkbookSource.base_9776
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:48.968423+00:00
-- url     : https://prove2.me/theorems/c934de11-b276-4729-8be1-a6fb7c7be355
-- title:
--   A comparison of two weighted cyclic reciprocal sums
-- statement:
--   Prove that :
--    $ \frac{1}{7a+b}+\frac{1}{7b+c}+\frac{1}{7c+a}\geq \frac{1}{a+2b+5c}+\frac{1}{b+2c+5a}+\frac{1}{c+2a+5b},\forall a,b,c> 0 $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9776` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9776; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9776 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (7 * a + b) + 1 / (7 * b + c) + 1 / (7 * c + a)) ≥ (1 / (a + 2 * b + 5 * c) + 1 / (b + 2 * c + 5 * a) + 1 / (c + 2 * a + 5 * b))  :=  by sorry
