-- Prove2me | Theorems.Thm_lean_workbook_plus_81768
-- name    : lean_workbook_plus_81768
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7adc31ca-339f-4fc1-acfe-72111a2d2c11
-- statement:
--   $ \omega^{3}-1=0\implies (\omega-1)(\omega^{2}+\omega+1)=0$ . Since $ \omega-1$ is not 0, $ \omega^{2}+\omega+1=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81768  (ω : ℂ)
  (h₀ : ω^3 = 1)
  (h₁ : ω ≠ 1) :
  ω^2 + ω + 1 = 0   :=  by sorry
