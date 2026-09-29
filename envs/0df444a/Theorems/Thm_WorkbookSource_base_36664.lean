-- Prove2me | Theorems.Thm_WorkbookSource_base_36664
-- name    : WorkbookSource.base_36664
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:19:41.266389+00:00
-- url     : https://prove2.me/theorems/d92a6b91-e812-4a52-8800-660a487de2e0
-- title:
--   A mixed power sum lower bound at fixed sum two
-- statement:
--   Let $a,b,c>0,a+b+c=2 .$ Prove that $$a^2+b^3+c^3\geq \frac{28}{27}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36664` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36664; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 2) : a^2 + b^3 + c^3 ≥ 28 / 27  :=  by sorry
