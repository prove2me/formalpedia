-- Prove2me | Theorems.Thm_lean_workbook_plus_33866
-- name    : lean_workbook_plus_33866
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6a02c1fd-49f0-4202-a570-b259f7ac9675
-- statement:
--   The sum of two numbers is $ 10$ ; their product is $ 20$ . The sum of their reciprocals is:
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33866 (x y : ℝ) (h₁ : x + y = 10) (h₂ : x*y = 20) : x⁻¹ + y⁻¹ = 0.5   :=  by sorry
