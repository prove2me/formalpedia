-- Prove2me | Theorems.Thm_WorkbookSource_base_13691
-- name    : WorkbookSource.base_13691
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:52.103021+00:00
-- url     : https://prove2.me/theorems/f4b7b998-2c18-49bb-936b-d296ee8f2d41
-- title:
--   A fifth-power sum bounds a mixed triple product
-- statement:
--   Let a, b, c > 0. Prove that: $ a^5 + b^5 + c^5 \geq a^2b^2c + ab^2c^2 + a^2c^2b $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13691` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13691; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13691 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^5 + b^5 + c^5 ≥ a^2 * b^2 * c + a * b^2 * c^2 + a^2 * c^2 * b  :=  by sorry
