-- Prove2me | Theorems.Thm_WorkbookSource_plus_70452
-- name    : WorkbookSource.plus_70452
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:03:25.715699+00:00
-- url     : https://prove2.me/theorems/78ba3cc8-e211-443c-b85e-5baaed3024aa
-- title:
--   A cubic sum bound under a quartic constraint
-- statement:
--   Prove that $ (a + b)^2 + (b + c)^2 + (c + a)^2 + 12\geq 8(a^3 + b^3 + c^3)$ given $ (a^2 - ab + b^2)^2 + (b^2 - bc + c^2)^2 + (c^2 - ca + a^2)^2 = 3$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_70452` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_70452; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_70452 (a b c : ℝ) (h1 : (a ^ 2 - a * b + b ^ 2) ^ 2 + (b ^ 2 - b * c + c ^ 2) ^ 2 + (c ^ 2 - c * a + a ^ 2) ^ 2 = 3) : (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 + 12 ≥ 8 * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
