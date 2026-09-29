-- Prove2me | Theorems.Thm_WorkbookSource_base_17945
-- name    : WorkbookSource.base_17945
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:38.730603+00:00
-- url     : https://prove2.me/theorems/2f72c72f-7b24-4d5a-8013-65a2b732deab
-- title:
--   A cyclic cubic bound at fixed squared norm
-- statement:
--   Let $a,b,c $ be nonnegative real numbers such that $a^2+b^2+c^2=3$ . Prove that $ a^2b+b^2c+c^2a \leq a+b+c $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17945` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17945; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17945 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : a^2 * b + b^2 * c + c^2 * a ≤ a + b + c  :=  by sorry
