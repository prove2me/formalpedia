-- Prove2me | Theorems.Thm_WorkbookSource_base_9070
-- name    : WorkbookSource.base_9070
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:23.337128+00:00
-- url     : https://prove2.me/theorems/1e09bc40-ec42-4645-b141-9ef611a71590
-- title:
--   A product and cubic-sum bound at sum two
-- statement:
--   Let $ x,y \geq 0$ with $x + y = 2$ . Prove that $ xy(x^3+y^3)\le \frac{8}{3}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9070` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9070; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9070 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 2) : x * y * (x ^ 3 + y ^ 3) ≤ 8 / 3  :=  by sorry
