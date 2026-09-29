-- Prove2me | Theorems.Thm_WorkbookSource_base_3531
-- name    : WorkbookSource.base_3531
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:26.858531+00:00
-- url     : https://prove2.me/theorems/2dc97e44-8a9e-46a6-b6c3-a94f50a08f52
-- title:
--   A product inequality for two quartic expressions
-- statement:
--   For reals $ x,y$ prove that:
--
--   $ \left[x^{2}\left(2x^{2} - 2x + 1\right) + 1\right]\left[y^{2}\left(2y^{2} - 2y + 1\right) + 1\right]\geq\left(2x^{2}y^{2} - xy(x + y) + 1\right)^{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3531` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3531; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3531 (x y : ℝ) : (x^2 * (2 * x^2 - 2 * x + 1) + 1) * (y^2 * (2 * y^2 - 2 * y + 1) + 1) ≥ (2 * x^2 * y^2 - x * y * (x + y) + 1)^2  :=  by sorry
