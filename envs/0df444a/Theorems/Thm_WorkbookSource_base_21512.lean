-- Prove2me | Theorems.Thm_WorkbookSource_base_21512
-- name    : WorkbookSource.base_21512
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:45.374984+00:00
-- url     : https://prove2.me/theorems/b002777e-d71a-404f-ba59-892635743101
-- title:
--   A cubed quadratic difference sum bounds squared cyclic differences
-- statement:
--   Prove the following inequality: $(x^2+y^2+z^2-xy-yz-zx)^3 \ge \frac{27}{4}(x-y)^2(y-z)^2(z-x)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21512` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21512; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21512 (x y z : ℝ) :
  (x^2 + y^2 + z^2 - x * y - x * z - y * z)^3 ≥ (27 / 4) * (x - y)^2 * (y - z)^2 * (z - x)^2  :=  by sorry
