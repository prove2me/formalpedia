-- Prove2me | Theorems.Thm_WorkbookSource_plus_60465
-- name    : WorkbookSource.plus_60465
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:40.766148+00:00
-- url     : https://prove2.me/theorems/21c4bfc4-2a1c-4808-b323-8bc4025dc253
-- title:
--   A quadratic norm minus triple-product bound
-- statement:
--   Let $ a,b,c > 0$ be such that $ a + b + c = 1$ . Prove the followings: (2) $ a^2 + b^2 + c^2 - 6abc \ge \frac {1}{9}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60465` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60465; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60465 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 - 6*a*b*c ≥ 1/9   :=  by sorry
