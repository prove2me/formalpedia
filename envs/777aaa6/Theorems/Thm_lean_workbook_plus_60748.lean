-- Prove2me | Theorems.Thm_lean_workbook_plus_60748
-- name    : lean_workbook_plus_60748
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/7f17694c-a420-4c2a-adf4-972d1bfc6b3d
-- statement:
--   Finally the number of good sequences is $3^{1959}\cdot \dfrac{3^{64}+1}{2}-2^{2023}+2^{2022}=\boxed {\dfrac{3^{2023}+3^{1959}}{2}-2^{2022}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60748 :
  (3^1959 * (3^64 + 1) / 2 - 2^2023 + 2^2022) = (3^2023 + 3^1959) / 2 - 2^2022   :=  by sorry
