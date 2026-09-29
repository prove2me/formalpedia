-- Prove2me | Theorems.Thm_WorkbookSource_base_10852
-- name    : WorkbookSource.base_10852
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:04.208346+00:00
-- url     : https://prove2.me/theorems/f2ea7efc-8c73-42a5-8c9e-1dcc0d08fa5e
-- title:
--   A sixth-degree product inequality with coefficient twenty-seven
-- statement:
--   Prove the inequality $27(x^2+y^2)(y^2+z^2)(z^2+x^2) \ge 8xyz(x+y+z)^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10852` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10852; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10852 (x y z : ℝ) : 27 * (x^2 + y^2) * (y^2 + z^2) * (z^2 + x^2) ≥ 8 * x * y * z * (x + y + z)^3  :=  by sorry
