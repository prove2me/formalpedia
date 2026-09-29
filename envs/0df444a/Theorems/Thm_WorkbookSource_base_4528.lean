-- Prove2me | Theorems.Thm_WorkbookSource_base_4528
-- name    : WorkbookSource.base_4528
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:01:08.392737+00:00
-- url     : https://prove2.me/theorems/0deccb27-3335-445e-b175-219a933dcd96
-- title:
--   An upper bound for a product of quadratic expressions
-- statement:
--   Prove that: $(a^{2}+a+1)(b^{2}+b+1)(c^{2}+c+1) \leq 27$ where $a;b;c$ are non-negative and satisfying $a+b+c=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4528` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4528; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4528 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : (a^2 + a + 1) * (b^2 + b + 1) * (c^2 + c + 1) ≤ 27  :=  by sorry
