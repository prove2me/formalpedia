-- Prove2me | Theorems.Thm_lean_workbook_plus_9883
-- name    : lean_workbook_plus_9883
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/79197f19-9a05-40da-a6be-165f1af7ceb2
-- statement:
--   prove that $ x^{x^2 + 2yz}y^{y^2 + 2xz}z^{z^2 + 2xy}\ge(xyz)^{xy + yz + zx}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9883 : ∀ x y z : ℝ, x^(x^2 + 2*y*z) * y^(y^2 + 2*x*z) * z^(z^2 + 2*x*y) ≥ (x*y*z)^(x*y + y*z + z*x)   :=  by sorry
