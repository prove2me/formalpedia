-- Prove2me | Theorems.Thm_lean_workbook_plus_75922
-- name    : lean_workbook_plus_75922
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/6e40011e-8904-4c0f-9e1b-f9344e88b6ed
-- statement:
--   Then $\dfrac{cos^5x}{cos(5x)}=\dfrac{cos^5x}{16cos^5x-20cos^3x+5cos(x)}=\dfrac{1}{16-10(1+tan^2x)+5(1+tan^2x)^2}$ giving \n\n $tan(5x)=\dfrac{5tan(x)-10tan^3x+tan^5x}{11+5tan^4x}$ or else \n\n $\dfrac{tan(5x)}{tan(x)}=\dfrac{5-10tan^2x+tan^4x}{11+5tan^4x}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75922 :
  ∀ x : ℝ, (cos x)^5 / cos (5 * x) = 1 / (16 - 10 * (1 + tan x ^ 2) + 5 * (1 + tan x ^ 2) ^ 2)   :=  by sorry
