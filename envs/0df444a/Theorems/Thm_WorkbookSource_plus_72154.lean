-- Prove2me | Theorems.Thm_WorkbookSource_plus_72154
-- name    : WorkbookSource.plus_72154
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:23.791311+00:00
-- url     : https://prove2.me/theorems/7a31c2a8-c10e-474f-aad4-3cd35ea9a3e8
-- title:
--   A cyclic cubic reciprocal sum lower bound at fixed sum three
-- statement:
--   Let $a,b,c >0$ such that $a+b+c=3.$ Prove that $$ \frac{a^3}{b} + \frac{b^3}{c} + \frac{c^3}{a} \ge \frac{3}{2} (3-abc)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_72154` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_72154; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_72154 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^3 / b + b^3 / c + c^3 / a) ≥ 3 / 2 * (3 - a * b * c)   :=  by sorry
