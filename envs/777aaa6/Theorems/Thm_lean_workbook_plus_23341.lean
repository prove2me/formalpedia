-- Prove2me | Theorems.Thm_lean_workbook_plus_23341
-- name    : lean_workbook_plus_23341
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7cfdc943-c768-4496-ad02-50df94f277e9
-- statement:
--   Expand and simplify the expression $(z_1+z_2+z_3+z_4+z_5)^3-3(z_1+z_2+z_3+z_4+z_5)(z_1^2+z_2^2+z_3^2+z_4^2+z_5^2)$ given that $z_1^2 + z_2^2 + z_3^2 + z_4^2 + z_5^2 = 0$ and $z_1 + z_2 + z_3 + z_4 + z_5 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23341 (z : ℂ → ℂ) (hz1 : ∑ i in Finset.range 5, z i = 0) (hz2 : ∑ i in Finset.range 5, z i ^ 2 = 0) : (∑ i in Finset.range 5, z i) ^ 3 - 3 * (∑ i in Finset.range 5, z i) * (∑ i in Finset.range 5, z i ^ 2) = 0   :=  by sorry
