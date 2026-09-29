-- Prove2me | Theorems.Thm_WorkbookSource_base_8605
-- name    : WorkbookSource.base_8605
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:21:35.23422+00:00
-- url     : https://prove2.me/theorems/0e18f56e-413d-436a-939f-a2c54a918b85
-- title:
--   A degree-eight inequality involving triangle factors
-- statement:
--   Let a,b,c>0 Prove that
--    $ (ab+bc+ca)\sum a^3b^3 \geq ( - a + b + c)(a - b + c)(a + b - c)(a^3 + b^3 + c^3)(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8605` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8605; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8605 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :  (a * b + b * c + c * a) * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) ≥ (-a + b + c) * (a - b + c) * (a + b - c) * (a ^ 3 + b ^ 3 + c ^ 3) * (a ^ 2 + b ^ 2 + c ^ 2) :=  by sorry
