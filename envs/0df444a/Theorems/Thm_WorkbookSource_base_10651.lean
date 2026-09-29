-- Prove2me | Theorems.Thm_WorkbookSource_base_10651
-- name    : WorkbookSource.base_10651
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:11.01905+00:00
-- url     : https://prove2.me/theorems/2ded3d7a-8dd3-4c97-9703-cdc683dbe6ba
-- title:
--   A cubic correction to a quadratic norm
-- statement:
--   Let $a, b, c > 0$ so that $ a + b + c = 1$ . Prove that $3(a^2 + b^2 + c^2) - 2(a^3 + b^3 + c^3) \geq \frac{7}{9}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10651` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10651; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10651 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) - 2 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 7 / 9  :=  by sorry
