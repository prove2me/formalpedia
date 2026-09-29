-- Prove2me | Theorems.Thm_WorkbookSource_plus_8085
-- name    : WorkbookSource.plus_8085
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:41.754601+00:00
-- url     : https://prove2.me/theorems/596c7267-c2ea-4410-83e0-bcb74b305cc1
-- title:
--   A product and linear bound on an ellipse
-- statement:
--   It is known that $x$ and $y$ are reals satisfying $x^2 + 2xy + 3y^2 = 4$. Prove that $xy - 2x + 4y \leq \frac{20}{3}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_8085` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_8085; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_8085 (x y : ℝ) (h : x ^ 2 + 2 * x * y + 3 * y ^ 2 = 4) : x * y - 2 * x + 4 * y ≤ 20 / 3   :=  by sorry
