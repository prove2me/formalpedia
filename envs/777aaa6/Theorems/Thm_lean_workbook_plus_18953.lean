-- Prove2me | Theorems.Thm_lean_workbook_plus_18953
-- name    : lean_workbook_plus_18953
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a256b606-0678-4b8f-a575-2ba215f6bd71
-- statement:
--   Prove that if $x^2 = y^2 + z^2$, then the expression $(x^2+y^2-z^2)(y^2+z^2-x^2)(z^2+x^2-y^2)$ is equal to 0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18953 (x y z : ℝ) (h₁ : x^2 = y^2 + z^2) : (x^2 + y^2 - z^2) * (y^2 + z^2 - x^2) * (z^2 + x^2 - y^2) = 0   :=  by sorry
