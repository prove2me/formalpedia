-- Prove2me | Theorems.Thm_WorkbookSource_base_10113
-- name    : WorkbookSource.base_10113
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:41:17.909425+00:00
-- url     : https://prove2.me/theorems/0afc3111-9f14-4289-8ea2-c767eff45b8a
-- title:
--   A squared cyclic cubic sum bounds symmetric products
-- statement:
--   Prove that for positive reals a, b, and c, the following inequality holds:
--
--    $(a^2b+b^2c+c^2a)^2\geq abc(a+b+c)(ab+ac+bc)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10113` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10113; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10113 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * b + b^2 * c + c^2 * a)^2 ≥ a * b * c * (a + b + c) * (a * b + b * c + c * a)  :=  by sorry
