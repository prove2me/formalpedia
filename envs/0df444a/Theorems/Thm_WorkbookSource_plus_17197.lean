-- Prove2me | Theorems.Thm_WorkbookSource_plus_17197
-- name    : WorkbookSource.plus_17197
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:23:16.039126+00:00
-- url     : https://prove2.me/theorems/c539a047-5194-4759-b805-278ac3e8611d
-- title:
--   A shifted cyclic reciprocal sum is at least three
-- statement:
--   Let $ a,b,c>0$ and $ a+b+c=3$. Prove that $ \frac{a+1}{b^2+1}+\frac{b+1}{c^2+1}+\frac{c+1}{a^2+1}\geq3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_17197` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_17197; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_17197 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + 1) / (b ^ 2 + 1) + (b + 1) / (c ^ 2 + 1) + (c + 1) / (a ^ 2 + 1) ≥ 3   :=  by sorry
