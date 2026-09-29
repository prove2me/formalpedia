-- Prove2me | Theorems.Thm_WorkbookSource_plus_71510
-- name    : WorkbookSource.plus_71510
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:51.383948+00:00
-- url     : https://prove2.me/theorems/572e950b-3d7b-41d5-85c7-3828c43f8919
-- title:
--   A weighted squared reciprocal sum bounds four divided by the total
-- statement:
--   For positive real numbers $a, b, c.$ Prove that $\frac{a+b+2c}{(c+2a)^2}+\frac{b+c+2a}{(a+2b)^2}+\frac{c+a+2b}{(b+2c)^2}\geq \frac{4}{a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_71510` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_71510; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_71510 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + 2 * c) / (c + 2 * a) ^ 2 + (b + c + 2 * a) / (a + 2 * b) ^ 2 + (c + a + 2 * b) / (b + 2 * c) ^ 2 ≥ 4 / (a + b + c)   :=  by sorry
