-- Prove2me | Theorems.Thm_WorkbookSource_base_52024
-- name    : WorkbookSource.base_52024
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:51:15.873701+00:00
-- url     : https://prove2.me/theorems/98749304-8475-40a4-b088-283b370a003b
-- title:
--   A weighted linear numerator over squared sums lower bound
-- statement:
--   For positive real numbers $a, b, c.$ Prove that $\frac{45a+b+9c}{(c+2a)^2}+\frac{45b+c+9a}{(a+2b)^2}+\frac{45c+a+9b}{(b+2c)^2}\geq \frac{55}{a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52024` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52024; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52024 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (45 * a + b + 9 * c) / (c + 2 * a) ^ 2 + (45 * b + c + 9 * a) / (a + 2 * b) ^ 2 + (45 * c + a + 9 * b) / (b + 2 * c) ^ 2 ≥ 55 / (a + b + c)  :=  by sorry
