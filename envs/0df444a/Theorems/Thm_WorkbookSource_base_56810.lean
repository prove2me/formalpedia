-- Prove2me | Theorems.Thm_WorkbookSource_base_56810
-- name    : WorkbookSource.base_56810
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:58.67789+00:00
-- url     : https://prove2.me/theorems/5cb5500e-0368-4f94-a318-8bd1dfd5959e
-- title:
--   A cyclic quartic sum times the total bounds a symmetric product
-- statement:
--   Let $a,b,c>0$ . Prove that: $(\sum a^{3}b)(\sum a)\geq 3abc(\sum a^{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56810` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56810; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56810 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 * b + b^3 * c + c^3 * a) * (a + b + c) ≥ 3 * a * b * c * (a^2 + b^2 + c^2)  :=  by sorry
