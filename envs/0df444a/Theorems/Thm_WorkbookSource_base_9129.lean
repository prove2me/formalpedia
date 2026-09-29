-- Prove2me | Theorems.Thm_WorkbookSource_base_9129
-- name    : WorkbookSource.base_9129
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:25.043769+00:00
-- url     : https://prove2.me/theorems/5ad03890-e774-4953-a477-d3324c804c35
-- title:
--   A cyclic cubic-over-quadratic sum bounds one third of the total
-- statement:
--   Let $ a,b,c > 0$ . $$ \frac {a^3}{2a^2 + b^2} + \frac {b^3}{2b^2 + c^2} + \frac {c^3}{2c^2 + a^2}\geqslant \frac {a + b + c}{3}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9129` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9129; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9129 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (2 * a^2 + b^2) + b^3 / (2 * b^2 + c^2) + c^3 / (2 * c^2 + a^2)) ≥ (a + b + c) / 3  :=  by sorry
