-- Prove2me | Theorems.Thm_WorkbookSource_base_35375
-- name    : WorkbookSource.base_35375
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:06.83037+00:00
-- url     : https://prove2.me/theorems/691fccd3-9f6a-43de-961b-27079c2192e1
-- title:
--   Three scaled quadratic factors bound a squared pairwise sum
-- statement:
--   For all reals $x$ , $y$ and $z$ prove that: $(2x^2+1)(2y^2+1)(2z^2+1)\geq3(xy+xz+yz)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35375` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35375; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35375 (x y z : ℝ) : (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) ≥ 3 * (x * y + x * z + y * z) ^ 2  :=  by sorry
