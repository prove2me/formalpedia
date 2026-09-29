-- Prove2me | Theorems.Thm_lean_workbook_plus_41982
-- name    : lean_workbook_plus_41982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/deafea6d-21f9-4a94-a1d1-48630e8726cd
-- statement:
--   Prove or disprove that for $x,y,z>0$ \n\n $$3\sum_{\text{cyc}} x^4 + 15\sum_{\text{cyc}} x^2y^2 \enspace \geq \enspace 6\sum_{\text{cyc}} x^3y + 6\sum_{\text{cyc}} xy^3+ 6\sum_{\text{cyc}} x^2yz$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41982 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 15 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ≥ 6 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + 6 * (x * y ^ 3 + y * z ^ 3 + z * x ^ 3) + 6 * (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y)   :=  by sorry
