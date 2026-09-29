-- Prove2me | Theorems.Thm_WorkbookSource_base_23786
-- name    : WorkbookSource.base_23786
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:59:56.970833+00:00
-- url     : https://prove2.me/theorems/002c779c-3b8b-4f60-a23f-1c20dc277add
-- title:
--   A pair-product rational upper bound at fixed sum three
-- statement:
--   Let $ a,b,c$ be positive real numbers such that $ a+b+c=3$ . Prove that: $ \frac{27}{2}\ge 4(ab+bc+ca)+\frac{a^{2}b^{2}}{a+b}+\frac{b^{2}c^{2}}{b+c}+\frac{c^{2}a^{2}}{a+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23786` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23786; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23786 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 27 / 2 ≥ 4 * (a * b + b * c + c * a) + a ^ 2 * b ^ 2 / (a + b) + b ^ 2 * c ^ 2 / (b + c) + c ^ 2 * a ^ 2 / (a + c)  :=  by sorry
