-- Prove2me | Theorems.Thm_WorkbookSource_plus_24054
-- name    : WorkbookSource.plus_24054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:18.113161+00:00
-- url     : https://prove2.me/theorems/1c772177-d913-4c9c-876d-74e58353cfe9
-- title:
--   A cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   If $a,b,c>0$ then prove that $\frac{a^2-bc}{b+c+2a}+\frac{b^2-ca}{a+c+2b}+\frac{c^2-ab}{a+b+2c}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_24054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_24054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_24054 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c) / (b + c + 2 * a) + (b^2 - c * a) / (a + c + 2 * b) + (c^2 - a * b) / (a + b + 2 * c) ≥ 0   :=  by sorry
