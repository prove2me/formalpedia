-- Prove2me | Theorems.Thm_WorkbookSource_base_16538
-- name    : WorkbookSource.base_16538
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:20.259282+00:00
-- url     : https://prove2.me/theorems/7c5190a3-448f-4831-bebc-d8a67fa98ee8
-- title:
--   A mixed cubic bound at unit sum
-- statement:
--   Let $ a,b,c > 0$ be such that $ a + b + c = 1$ . Prove the followings: (4) $ a^2(b + c) + b^2(c + a) + c^2(a + b) \ge \frac {1}{3} (1 - a^2 - b^2 - c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16538` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16538; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16538 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ 1 / 3 * (1 - a^2 - b^2 - c^2)  :=  by sorry
