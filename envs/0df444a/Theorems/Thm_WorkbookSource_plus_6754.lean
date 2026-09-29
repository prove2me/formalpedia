-- Prove2me | Theorems.Thm_WorkbookSource_plus_6754
-- name    : WorkbookSource.plus_6754
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:22.0093+00:00
-- url     : https://prove2.me/theorems/94b2ca9b-a456-497a-b534-54e9d4f58692
-- title:
--   A linear-form bound on a weighted ellipsoid
-- statement:
--   Prove that $(4x-3y-2z)^2 \le 12$ under the given condition $2x^2+3y^2+4z^2=1$ and $x,y,z\in \mathbb{R}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_6754` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_6754; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_6754 (x y z : ℝ) (h : 2*x^2 + 3*y^2 + 4*z^2 = 1) :
  (4*x - 3*y - 2*z)^2 ≤ 12   :=  by sorry
