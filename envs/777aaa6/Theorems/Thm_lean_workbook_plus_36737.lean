-- Prove2me | Theorems.Thm_lean_workbook_plus_36737
-- name    : lean_workbook_plus_36737
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/98d6a2e1-a867-4460-b127-9118de151f28
-- statement:
--   Set $u=y+z$ then $1\le xu+\frac{u^2}4 \implies x\ge \frac{4-u^2}{4u}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36737  (x y z u : ℝ)
  (h₀ : 0 < u)
  (h₁ : u = y + z)
  (h₂ : 1 ≤ x * u + u^2 / 4) :
  x ≥ (4 - u^2) / (4 * u)   :=  by sorry
