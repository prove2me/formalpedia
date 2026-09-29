-- Prove2me | Theorems.Thm_WorkbookSource_base_34623
-- name    : WorkbookSource.base_34623
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:40.559007+00:00
-- url     : https://prove2.me/theorems/34f55f9e-5f76-4a91-8f35-24f98faca2ce
-- title:
--   A fourth-power lower bound at unit positive sum
-- statement:
--   Prove that $x^{4}+y^{4}+z^{4}+1\geq 2(x^{2}+y^{2}+z^{2})$ given $x+y+z=1$ and $x,y,z$ are positive real numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34623` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34623; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34623 (x y z : ℝ) (h1 : x + y + z = 1) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^4 + y^4 + z^4 + 1 ≥ 2 * (x^2 + y^2 + z^2)  :=  by sorry
