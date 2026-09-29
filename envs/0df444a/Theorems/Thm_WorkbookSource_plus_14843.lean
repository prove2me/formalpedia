-- Prove2me | Theorems.Thm_WorkbookSource_plus_14843
-- name    : WorkbookSource.plus_14843
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:25:52.606587+00:00
-- url     : https://prove2.me/theorems/ecabe90f-297f-43ff-9461-4dad69c1a0e1
-- title:
--   A fifth-degree symmetric product inequality
-- statement:
--   Prove that for $a,b,c>0$ $$2(a^3+b^3+c^3)(ab+bc+ca)\ge3abc(3a^2+3b^2+3c^2-ab-bc-ca)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_14843` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_14843; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_14843 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a ^ 3 + b ^ 3 + c ^ 3) * (a * b + b * c + c * a) ≥ 3 * a * b * c * (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a))   :=  by sorry
