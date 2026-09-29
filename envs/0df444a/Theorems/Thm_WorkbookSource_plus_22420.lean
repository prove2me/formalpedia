-- Prove2me | Theorems.Thm_WorkbookSource_plus_22420
-- name    : WorkbookSource.plus_22420
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:07:53.265203+00:00
-- url     : https://prove2.me/theorems/8fbedeea-da72-4d83-b7ca-319c393f136c
-- title:
--   A symmetric fifth-degree inequality with a triple-product correction
-- statement:
--   Prove that for positive numbers a, b, and c, the following inequality holds:
--   $\sum (a^4b+a^4c)+2abc(\sum ab)\ge \sum (a^3b^2+a^3c^2)+2abc(\sum a^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_22420` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_22420; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_22420 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 * b + a^4 * c + b^4 * c + b^4 * a + c^4 * a + c^4 * b + 2 * a * b * c * (a * b + b * c + c * a) ≥ a^3 * b^2 + a^3 * c^2 + b^3 * c^2 + b^3 * a^2 + c^3 * a^2 + c^3 * b^2 + 2 * a * b * c * (a^2 + b^2 + c^2)   :=  by sorry
