-- Prove2me | Theorems.Thm_lean_workbook_plus_50838
-- name    : lean_workbook_plus_50838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ef5fa301-26b7-41c0-b379-cdca2d01ca9c
-- statement:
--   Given the identity $(a+b+c)^2 - \frac{3}{2}(a(b+c)+b(c+a)+c(a+b)) = \frac{1}{2}((a-b)^2 + (b-c)^2 + (c-a)^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50838 : ∀ a b c : ℝ, (a+b+c)^2 - (3/2)*(a*(b+c) + b*(c+a) + c*(a+b)) = (1/2)*((a-b)^2 + (b-c)^2 + (c-a)^2)   :=  by sorry
