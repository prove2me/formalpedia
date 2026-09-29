-- Prove2me | Theorems.Thm_lean_workbook_plus_19731
-- name    : lean_workbook_plus_19731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0ca35ebf-1ad0-490d-8511-b328a6192398
-- statement:
--   If $x+y+z=x^3+y^3+z^3=0$ then $xyz=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19731 (x y z: ℝ) (h₁ : x + y + z = 0) (h₂ : x^3 + y^3 + z^3 = 0) : x*y*z = 0   :=  by sorry
