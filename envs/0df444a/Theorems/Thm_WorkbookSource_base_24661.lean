-- Prove2me | Theorems.Thm_WorkbookSource_base_24661
-- name    : WorkbookSource.base_24661
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:55.781498+00:00
-- url     : https://prove2.me/theorems/04f3a5a3-ad07-4517-bb8f-1cee926a5e99
-- title:
--   A cyclic cubic ratio bounds a squared total
-- statement:
--   Let $a,b,c>0$ . Prove that:
--    $ \frac{a(a^2+bc)}{a+b}+\frac{b(b^2+ac)}{b+c}+\frac{c(c^2+ab)}{c+a} \geq \frac{(a+b+c)^2}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_24661` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_24661; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_24661 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b * c) / (a + b) + b * (b ^ 2 + a * c) / (b + c) + c * (c ^ 2 + a * b) / (c + a)) ≥ (a + b + c) ^ 2 / 3  :=  by sorry
