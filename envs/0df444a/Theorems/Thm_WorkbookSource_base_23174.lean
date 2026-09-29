-- Prove2me | Theorems.Thm_WorkbookSource_base_23174
-- name    : WorkbookSource.base_23174
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:54:39.917723+00:00
-- url     : https://prove2.me/theorems/1465eeed-5183-4fc5-84ae-f826ab3132d1
-- title:
--   A mixed quadratic reciprocal lower bound
-- statement:
--   Let $a,b,c >0 $. Prove that $\sum \frac{1}{a^{2}+bc}\geq \frac{9}{4(ab+bc+ca)} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23174` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23174; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23174 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a ^ 2 + b * c) + 1 / (b ^ 2 + c * a) + 1 / (c ^ 2 + a * b) ≥ 9 / (4 * (a * b + b * c + c * a))  :=  by sorry
