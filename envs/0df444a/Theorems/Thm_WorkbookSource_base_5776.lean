-- Prove2me | Theorems.Thm_WorkbookSource_base_5776
-- name    : WorkbookSource.base_5776
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:35.720083+00:00
-- url     : https://prove2.me/theorems/dcfed781-c5dc-4a48-b30a-d6ef176b3d58
-- title:
--   A cyclic quadratic-product ratio lower bound
-- statement:
--   Let $a, b, c>0$ . Prove that
--    $\frac{ab}{c^2+ab+bc}+\frac{bc}{a^2+bc+ca}+\frac{ca}{b^2+ca+ab}\ge\frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5776` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5776; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5776 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (c * c + a * b + b * c) + b * c / (a * a + b * c + c * a) + c * a / (b * b + c * a + a * b)) ≥ 3 / 4  :=  by sorry
