-- Prove2me | Theorems.Thm_lean_workbook_plus_37502
-- name    : lean_workbook_plus_37502
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/78b27888-72b8-43b2-a86d-901366ecd403
-- statement:
--   Let $y=2z$, thus we have: $(x+2)^{4}-x^{4}=y^{3}\iff x^{3}+3x^{2}+4x+2=z^{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37502 (x y z: ℤ) (h₁ : y = 2 * z) : (x + 2) ^ 4 - x ^ 4 = y ^ 3 ↔ x ^ 3 + 3 * x ^ 2 + 4 * x + 2 = z ^ 3   :=  by sorry
