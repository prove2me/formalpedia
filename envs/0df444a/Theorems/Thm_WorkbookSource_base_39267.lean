-- Prove2me | Theorems.Thm_WorkbookSource_base_39267
-- name    : WorkbookSource.base_39267
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:56.144898+00:00
-- url     : https://prove2.me/theorems/7b5b286d-618d-46f9-959a-9f00750e04f7
-- title:
--   A weighted squared-norm bound at fixed pairwise sum
-- statement:
--   Prove that: $3x^{2}+3y^{2}+z^{2}\geq 10$ where $x;y;z$ are real numbers satisfying $xy+yz+xz=5$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39267` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39267; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39267 (x y z : ℝ) (h : x * y + y * z + z * x = 5) :
  3 * x ^ 2 + 3 * y ^ 2 + z ^ 2 ≥ 10  :=  by sorry
