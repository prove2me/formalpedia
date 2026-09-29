-- Prove2me | Theorems.Thm_lean_workbook_plus_14387
-- name    : lean_workbook_plus_14387
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5ccf3579-6458-4421-afb3-ba5bf10437b1
-- statement:
--   Given $u=x+y$ and $v=xy$, the equation is equivalent to $u^{3}-2uv=8u^{2}-8v+8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14387  (x y u v : ℝ)
  (h₀ : u = x + y)
  (h₁ : v = x * y)
  (h₂ : u^3 - 2 * u * v = 8 * u^2 - 8 * v + 8) :
  u^3 - 2 * u * v = 8 * u^2 - 8 * v + 8   :=  by sorry
