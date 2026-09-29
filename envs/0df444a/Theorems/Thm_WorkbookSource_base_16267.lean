-- Prove2me | Theorems.Thm_WorkbookSource_base_16267
-- name    : WorkbookSource.base_16267
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:13.585987+00:00
-- url     : https://prove2.me/theorems/e17d0ede-8024-4e78-a694-1a95aecd4a40
-- title:
--   An affine product bound on an ellipse
-- statement:
--   Prove that $xy - 2x + 5y\leq \frac{13}{4}$ given $5x^2 + 4xy + 11y^2 = 3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16267` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16267; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16267 (x y : ℝ) (h : 5 * x ^ 2 + 4 * x * y + 11 * y ^ 2 = 3) :
  x * y - 2 * x + 5 * y ≤ 13 / 4  :=  by sorry
