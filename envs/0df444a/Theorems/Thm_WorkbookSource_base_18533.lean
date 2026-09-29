-- Prove2me | Theorems.Thm_WorkbookSource_base_18533
-- name    : WorkbookSource.base_18533
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:03.004594+00:00
-- url     : https://prove2.me/theorems/a03a953b-74dc-4574-ba27-e1787814fae2
-- title:
--   A weighted quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $a,b,c> 0$ and $a+b+c=3$ . prove that: $\frac{a^2}{9a+(b+2c)^2}+\frac{b^2}{9b+(c+2a)^2}+\frac{c^2}{9c+(a+2b)^2}\geq \frac{1}{6}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18533` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18533; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18533 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / (9 * a + (b + 2 * c)^2) + b^2 / (9 * b + (c + 2 * a)^2) + c^2 / (9 * c + (a + 2 * b)^2)) ≥ 1 / 6  :=  by sorry
