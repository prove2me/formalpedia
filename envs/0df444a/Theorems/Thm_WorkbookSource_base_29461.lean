-- Prove2me | Theorems.Thm_WorkbookSource_base_29461
-- name    : WorkbookSource.base_29461
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:15.785886+00:00
-- url     : https://prove2.me/theorems/9aea84ca-846b-4819-aae3-415bb019aa72
-- title:
--   A weighted pairwise product bound at unit sum
-- statement:
--   a, b and c are positive real numbers such that a+b+c = 1. Prove the following inequality:
--
--    $ ab + 2bc + 3ac \le \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29461` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29461; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29461 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a * b + 2 * b * c + 3 * a * c ≤ 3 / 4  :=  by sorry
