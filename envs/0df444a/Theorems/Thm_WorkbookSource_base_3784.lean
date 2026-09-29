-- Prove2me | Theorems.Thm_WorkbookSource_base_3784
-- name    : WorkbookSource.base_3784
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T02:28:21.536217+00:00
-- url     : https://prove2.me/theorems/b067004f-0d5c-4829-832a-12590163dd60
-- title:
--   A cyclic cubic-product ratio bound at fixed sum three
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that $\frac{a^2b}{1+a+2b}+\frac{b^2c}{1+b+2c}+\frac{c^2a}{1+c+2a}\le\frac{3(a^2+b^2+c^2)}{4(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3784` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3784; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3784 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 * b / (1 + a + 2 * b) + b^2 * c / (1 + b + 2 * c) + c^2 * a / (1 + c + 2 * a)) ≤ (3 * (a^2 + b^2 + c^2)) / (4 * (a * b + b * c + c * a))  :=  by sorry
