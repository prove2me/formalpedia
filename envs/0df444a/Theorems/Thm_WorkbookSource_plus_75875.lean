-- Prove2me | Theorems.Thm_WorkbookSource_plus_75875
-- name    : WorkbookSource.plus_75875
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:39.125364+00:00
-- url     : https://prove2.me/theorems/274912dd-e9e4-466d-9a65-bc2300635291
-- title:
--   A squared pairwise-product bound under lower bounds
-- statement:
--   Prove that for positive numbers a, b, and c such that a + b + c = 3 and a, b, c are greater than or equal to 2/3, the following inequality holds: \(\sum_{cyc} (ab)^2 \ge \sum_{cyc} ab\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75875` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75875; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75875 {a b c : ℝ} (ha : 2/3 ≤ a) (hb : 2/3 ≤ b) (hc : 2/3 ≤ c) (hab : a + b + c = 3) : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
