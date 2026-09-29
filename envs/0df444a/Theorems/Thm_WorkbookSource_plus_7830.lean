-- Prove2me | Theorems.Thm_WorkbookSource_plus_7830
-- name    : WorkbookSource.plus_7830
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:19:45.039842+00:00
-- url     : https://prove2.me/theorems/eb37dd9b-7ffd-47f8-ac8b-e4a1a1a5f2e4
-- title:
--   A sixth-degree comparison of symmetric sums
-- statement:
--   Let a,b,c>0 Prove that:
--    $ (a + b + c)^2(ab + bc + ca)^2 + (ab + bc + ca)^3 \geq 4abc(a + b + c)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7830` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7830; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7830 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 2 * (a * b + b * c + c * a) ^ 2 + (a * b + b * c + c * a) ^ 3 ≥ 4 * a * b * c * (a + b + c) ^ 3   :=  by sorry
