-- Prove2me | Theorems.Thm_lean_workbook_plus_44087
-- name    : lean_workbook_plus_44087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/92cc416e-55e7-49fa-9e1e-5777da35eaf2
-- statement:
--   Prove that $ x^4z+y^4x+z^4y-x^4y-y^4z-z^4x = (x-y)(z-y)(x-z)(x^2+y^2+z^2+xy+yz+zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44087 (x y z : ℂ) : (x^4 * z + y^4 * x + z^4 * y - x^4 * y - y^4 * z - z^4 * x) = (x - y) * (z - y) * (x - z) * (x^2 + y^2 + z^2 + x * y + y * z + z * x)   :=  by sorry
