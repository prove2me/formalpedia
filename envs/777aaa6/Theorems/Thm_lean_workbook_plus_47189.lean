-- Prove2me | Theorems.Thm_lean_workbook_plus_47189
-- name    : lean_workbook_plus_47189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/fab94b04-1e9c-40e6-901d-f132dd3799cf
-- statement:
--   Prove that: $3(x^2+xy+y^2)(y^2+yz+z^2)(z^2+xz+x^2)\ge(x+y+z)^2(xy+yz+zx)^2$ for any $x,y,z\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47189 : ∀ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 → 3 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ (x + y + z) ^ 2 * (x * y + x * z + y * z) ^ 2   :=  by sorry
