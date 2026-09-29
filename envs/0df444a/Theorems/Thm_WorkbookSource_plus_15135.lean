-- Prove2me | Theorems.Thm_WorkbookSource_plus_15135
-- name    : WorkbookSource.plus_15135
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:38.151982+00:00
-- url     : https://prove2.me/theorems/adbd3003-f926-4158-925e-0a15bfff846f
-- title:
--   An asymmetric quadratic lower bound at sum three
-- statement:
--   Let $a, b, c$ be nonnegative real numbers such that $a + b + c = 3.$ Prove that
--
--    $$a^2+\frac{1}{2}b^2+c^2+ab+ca\geq 3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_15135` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_15135; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_15135 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3) : a^2 + (1 / 2) * b^2 + c^2 + a * b + c * a ≥ 3   :=  by sorry
