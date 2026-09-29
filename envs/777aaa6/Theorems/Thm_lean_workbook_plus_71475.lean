-- Prove2me | Theorems.Thm_lean_workbook_plus_71475
-- name    : lean_workbook_plus_71475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/47af19f4-b7f8-4d84-b9f5-22fb5d54ebb4
-- statement:
--   The formula for the cost of Tony's Towing Service is $30+1.75m$, where $m$ is the number of miles that the car is towed. We want to solve the equation $30+1.75m=59.75$ for $m$. We get: $30+1.75m = 59.75 \implies 1.75m = 29.75 \implies m = \boxed{17}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71475  (m : ℝ)
  (h₀ : 30 + 1.75 * m = 59.75) :
  m = 17   :=  by sorry
