-- Prove2me | Theorems.Thm_lean_workbook_plus_74717
-- name    : lean_workbook_plus_74717
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/31c5df65-5c49-4713-a27a-38dee4c8f6ae
-- statement:
--   $$\frac{2xy}{(z+x)(z+y)}+\frac{2yz}{(x+y)(x+z)}+\frac{3zx}{(y+z)(x+y)}\geq \frac{5}{3}\iff x(y-2z)^2+y(z-x)^2+z(2x-y)^2\geq 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74717 : ∀ x y z : ℝ, (2*x*y/((z+x)*(z+y)) + 2*y*z/((x+y)*(x+z)) + 3*z*x/((y+z)*(x+y)) ≥ 5/3 ↔ x*(y-2*z)^2 + y*(z-x)^2 + z*(2*x-y)^2 ≥ 0)   :=  by sorry
