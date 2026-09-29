-- Prove2me | Theorems.Thm_lean_workbook_plus_26700
-- name    : lean_workbook_plus_26700
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0d49f0bd-2c13-41f8-9185-71bc0bbd01cf
-- statement:
--   $(x^{2}+y^{2}+z^{2})^{2n}+3^{2n}+2(3(x^{2}+y^{2}+z^{2}))^{n}\ge 2(xy+yz+zx)^{2n}+2(x+y+z)^{2n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26700 ∀ x y z n : ℝ, (x^2 + y^2 + z^2)^2 * n + 3^2 * n + 2 * (3 * (x^2 + y^2 + z^2))^n ≥ 2 * (x * y + y * z + z * x)^2 * n + 2 * (x + y + z)^2 * n   :=  by sorry
