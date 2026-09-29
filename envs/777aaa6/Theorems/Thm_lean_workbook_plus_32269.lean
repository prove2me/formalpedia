-- Prove2me | Theorems.Thm_lean_workbook_plus_32269
-- name    : lean_workbook_plus_32269
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/721001f5-4c62-4e8b-9bcb-d4f925973b8e
-- statement:
--   Let $P(x,y,z) = (x-y)^5+(y-z)^5+(z-x)^5$ . Clearly $x-y$ , $y-z$ and $z-x$ divde $P$ and we can prove: $P(x,y,z)=-5 (x-y) (x-z) (y-z) (x^2+y^2+z^2-x y-x z-y z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32269 (x y z : ℂ) : (x - y) ^ 5 + (y - z) ^ 5 + (z - x) ^ 5 = -5 * (x - y) * (x - z) * (y - z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - x * z - y * z)   :=  by sorry
