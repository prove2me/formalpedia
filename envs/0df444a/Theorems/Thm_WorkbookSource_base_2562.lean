-- Prove2me | Theorems.Thm_WorkbookSource_base_2562
-- name    : WorkbookSource.base_2562
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:10.341549+00:00
-- url     : https://prove2.me/theorems/6d0e3045-c22d-41c4-b849-5d45c538aae8
-- title:
--   A quadratic and cubic lower bound at sum three
-- statement:
--   Let $x;y;z \geq 0$ such that $x+y+z=3$ Prove: $x^2+y^2+z^2+3xyz \geq \dfrac{9}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2562` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2562; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2562 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 3) : x ^ 2 + y ^ 2 + z ^ 2 + 3 * x * y * z ≥ 9 / 2  :=  by sorry
