-- Prove2me | Theorems.Thm_WorkbookSource_base_747
-- name    : WorkbookSource.base_747
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:10:33.083247+00:00
-- url     : https://prove2.me/theorems/dff5f787-2f9b-4432-8235-11afd8eb53df
-- title:
--   A cubic-sum product bound on the unit sphere
-- statement:
--   Let $a,b,c \in \mathbb{R}$ such that $a^2+b^2+c^2=1$ . Prove that $$(a+b+c)(a^3+b^3+c^3) \leq \frac{5}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_747` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_747; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_747 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : (a + b + c) * (a^3 + b^3 + c^3) ≤ 5 / 4  :=  by sorry
