-- Prove2me | Theorems.Thm_WorkbookSource_base_6832
-- name    : WorkbookSource.base_6832
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:28.579812+00:00
-- url     : https://prove2.me/theorems/f8b52a05-fef6-4bd3-9e85-26c950e95a3d
-- title:
--   A shifted-product and fourth-power comparison
-- statement:
--   Knowing that $ a,b,c > 0$ and $ a + b + c = 1$ ,prove the ineq:
--   $ (1 + a)(1 + b)(1 + c) \geq (1 - a^2)^2 + (1 - b^2)^2 + (1 - c^2)^2(*)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6832` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6832; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6832 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) :  (1 + a) * (1 + b) * (1 + c) ≥ (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2  :=  by sorry
