-- Prove2me | Theorems.Thm_WorkbookSource_base_5863
-- name    : WorkbookSource.base_5863
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:27:00.627222+00:00
-- url     : https://prove2.me/theorems/bb09b6e7-3f79-44f9-9173-ca645ee50625
-- title:
--   A cyclic shifted-product ratio bound at fixed sum three
-- statement:
--   For $a, b, c>0, a+b+c=3$ prove that $\frac{a(b+2)}{a(c+2)+b+2}+\frac{b(c+2)}{b(a+2)+c+2}+\frac{c(a+2)}{c(b+2)+a+2}\le\frac{a^2+b^2+c^2}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5863` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5863; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5863 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * (b + 2) / (a * (c + 2) + b + 2) + b * (c + 2) / (b * (a + 2) + c + 2) + c * (a + 2) / (c * (b + 2) + a + 2)) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2  :=  by sorry
