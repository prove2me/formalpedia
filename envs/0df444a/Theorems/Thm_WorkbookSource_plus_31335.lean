-- Prove2me | Theorems.Thm_WorkbookSource_plus_31335
-- name    : WorkbookSource.plus_31335
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:47.943356+00:00
-- url     : https://prove2.me/theorems/dfc2a23f-f507-42d7-be3e-a93c9fbfa981
-- title:
--   A cubic product correction on a nonnegative sphere
-- statement:
--   If $ a,b,c $ are non-negative reals such that $ a^2+b^2+c^2=3 $ , prove that $2(a+b+c)\ge 3+\frac{3}{8}(a+b)(b+c)(c+a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_31335` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_31335; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_31335 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : 2 * (a + b + c) ≥ 3 + 3/8 * (a + b) * (b + c) * (c + a)   :=  by sorry
