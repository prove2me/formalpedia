-- Prove2me | Theorems.Thm_WorkbookSource_base_29420
-- name    : WorkbookSource.base_29420
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:55.409756+00:00
-- url     : https://prove2.me/theorems/14b894e6-5a7b-4558-acbe-a829d91f9b5a
-- title:
--   A cubic bound under three triangle-style affine constraints
-- statement:
--   Let $a,b,c$ be non-negative real numbers such that $a+b\leq c+1, b+c\leq a+1$ and $c+a\leq b+1.$ Show that
--    $a^2+b^2+c^2\leq 2abc+1.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29420` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29420; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29420 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b ≤ c + 1) (hbc : b + c ≤ a + 1) (hca : c + a ≤ b + 1) : a^2 + b^2 + c^2 ≤ 2 * a * b * c + 1  :=  by sorry
