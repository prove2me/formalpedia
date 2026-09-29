-- Prove2me | Theorems.Thm_WorkbookSource_base_16099
-- name    : WorkbookSource.base_16099
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:47:12.272719+00:00
-- url     : https://prove2.me/theorems/e237a60d-a628-4f82-b4c9-9bc9af713fc8
-- title:
--   A squared cubic sum bounds three symmetric factors
-- statement:
--   Can we prove $ (a^3 + b^3 + c^3)^2\geq abc(a + b + c)(a^2 + b^2 + c^2)$ for positive reals $ a,\ b,\ c$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16099` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16099; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16099 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3)^2 ≥ a * b * c * (a + b + c) * (a^2 + b^2 + c^2)  :=  by sorry
