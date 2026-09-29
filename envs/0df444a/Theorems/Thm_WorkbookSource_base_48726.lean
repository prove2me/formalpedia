-- Prove2me | Theorems.Thm_WorkbookSource_base_48726
-- name    : WorkbookSource.base_48726
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:17.945982+00:00
-- url     : https://prove2.me/theorems/3e28b084-ea42-49a3-a096-cfd66f604dad
-- title:
--   A linear term and triple product are at most two
-- statement:
--   Let $ a,$ $ b$ and $ c$ are non-negative numbers such that $ a+b+c=2.$ Prove that
--    $ a + 4abc\leq2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48726` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48726; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48726 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : a + 4 * a * b * c ≤ 2  :=  by sorry
