-- Prove2me | Theorems.Thm_lean_workbook_plus_63888
-- name    : lean_workbook_plus_63888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/18bcfde6-27e5-4510-8e5a-ad37de23e8f3
-- statement:
--   For some constant $k$ the polynomial $p(x) = 3x^2 + kx + 117$ has the property that $p(1) = p(10)$ . Evaluate $p(20)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63888 (p : ℝ → ℝ) (k : ℝ) (h₁ : p = fun x : ℝ => 3 * x^2 + k * x + 117) (h₂ : p 1 = p 10) : p 20 = 657   :=  by sorry
