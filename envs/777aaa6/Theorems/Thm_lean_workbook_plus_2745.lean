-- Prove2me | Theorems.Thm_lean_workbook_plus_2745
-- name    : lean_workbook_plus_2745
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ac1d31be-11fb-4415-889a-a00dc1c1eda5
-- statement:
--   $ \implies$ $ x^{6} + y^{6} + z^{6}\geq x^{4}yz + y^{4}zx + z^{4}xy$ which is obviously true by Muirhead
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2745 (x y z : ℝ) : x^6 + y^6 + z^6 ≥ x^4*y*z + y^4*z*x + z^4*x*y   :=  by sorry
