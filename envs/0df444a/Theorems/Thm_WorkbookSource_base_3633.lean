-- Prove2me | Theorems.Thm_WorkbookSource_base_3633
-- name    : WorkbookSource.base_3633
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:10:54.074015+00:00
-- url     : https://prove2.me/theorems/2c18d904-8e51-4e93-8872-012f199b7475
-- title:
--   A cyclic product reciprocal lower bound
-- statement:
--   Let $a, b, c>0$ .
--    $$\frac{1}{b(a+b)}+\frac{1}{c(b+c)}+\frac{1}{a(a+c)}\geq \frac{9}{2(ab+bc+ca)}.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3633` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3633; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3633 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (b * (a + b)) + 1 / (c * (b + c)) + 1 / (a * (a + c))) ≥ 9 / (2 * (a * b + b * c + c * a))  :=  by sorry
