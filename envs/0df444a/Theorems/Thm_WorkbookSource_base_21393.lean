-- Prove2me | Theorems.Thm_WorkbookSource_base_21393
-- name    : WorkbookSource.base_21393
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:06.449033+00:00
-- url     : https://prove2.me/theorems/5b3e49ea-4eea-4079-a0ae-50a45ec904a8
-- title:
--   A two-variable quartic inequality with lower-degree terms
-- statement:
--   Let $x,y>0$ .Prove that ${{x}^{3}}y+x{{y}^{3}}+1\ge x{{y}^{2}}+{{x}^{2}}y+xy.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21393` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21393; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21393 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 * y + x * y^3 + 1 ≥ x^2 * y + x * y^2 + x * y  :=  by sorry
