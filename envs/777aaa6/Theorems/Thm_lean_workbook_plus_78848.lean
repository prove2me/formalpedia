-- Prove2me | Theorems.Thm_lean_workbook_plus_78848
-- name    : lean_workbook_plus_78848
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3b5ba751-e2a4-4bb6-b5ad-f36a98cba7a2
-- statement:
--   $\sin(a+b)\sin(a-b)=\frac{(e^{i(a+b)}-e^{-i(a+b)})(e^{i(b-a)}-e^{i(a-b)})}{4}=\frac{e^{2ib}+e^{-2ib}-e^{2ia}-e^{-2ia}}{4}=\frac{(e^{ib}-e^{-ib})^2-(e^{ia}-e^{-ia})^2}{4}=\sin^2(a)-\sin^2(b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78848 (a b : ℝ) : (Real.sin (a + b) * Real.sin (a - b)) = (Real.sin a ^ 2 - Real.sin b ^ 2)   :=  by sorry
