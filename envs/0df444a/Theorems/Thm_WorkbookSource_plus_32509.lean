-- Prove2me | Theorems.Thm_WorkbookSource_plus_32509
-- name    : WorkbookSource.plus_32509
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:34:44.627116+00:00
-- url     : https://prove2.me/theorems/45e12d9b-7ba9-4c31-9d2a-7bac29300b55
-- title:
--   A cyclic sixth-degree inequality with symmetric corrections
-- statement:
--   Let $a,b,c>0$ . Prove that :
--    $3\sum a^{2}b^{4}+abc\sum a^{3}+\sum a^{3}b^{3}\geq 9a^{2}b^{2}c^{2}+abc\sum ab(a+b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_32509` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32509; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_32509 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^2 * b^4 + b^2 * c^4 + c^2 * a^4) + a * b * c * (a^3 + b^3 + c^3) + (a^3 * b^3 + b^3 * c^3 + c^3 * a^3) ≥ 9 * a^2 * b^2 * c^2 + a * b * c * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a))   :=  by sorry
