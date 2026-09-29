-- Prove2me | Theorems.Thm_lean_workbook_plus_80536
-- name    : lean_workbook_plus_80536
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/950ec822-7997-44aa-a454-07fd6fbe9ff3
-- statement:
--   $ =\frac{e^{-t^2}}{4}\left(\sqrt\pi+\sqrt\pi\right)=\frac{\sqrt\pi\,e^{-t^2}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80536 (t : ℝ) : (1/4) * (Real.sqrt π + Real.sqrt π) * (e^(-t^2)) = (Real.sqrt π / 2) * e^(-t^2)   :=  by sorry
