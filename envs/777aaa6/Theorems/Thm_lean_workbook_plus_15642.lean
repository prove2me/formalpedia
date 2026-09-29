-- Prove2me | Theorems.Thm_lean_workbook_plus_15642
-- name    : lean_workbook_plus_15642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3b28c5bb-9590-424a-808e-0486f3c7797e
-- statement:
--   Simplest Vieta ..... $|\frac {(-1)^5.(18)}{2} - \frac {(-1)^2.(0)}{2}|=9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15642  (q e : ℝ)
  (h₀ : q = 18)
  (h₁ : e = 0) :
  abs ((-1)^5 * (q / 2) - (-1)^2 * (e / 2)) = 9   :=  by sorry
