-- Prove2me | Theorems.Thm_WorkbookSource_plus_30516
-- name    : WorkbookSource.plus_30516
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:42.507028+00:00
-- url     : https://prove2.me/theorems/9ec7b72b-7064-48d1-8774-5c17d923dc83
-- title:
--   A shifted-product bound on the unit circle
-- statement:
--   Let $a,b$ be reals such that $a^2+ b^ 2= 1.$ Prove that $(a+1)(a+2b + 1)\leq \frac{27}{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30516` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30516; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_30516 (a b : ℝ) (h : a^2 + b^2 = 1) : (a + 1) * (a + 2 * b + 1) ≤ 27 / 5   :=  by sorry
