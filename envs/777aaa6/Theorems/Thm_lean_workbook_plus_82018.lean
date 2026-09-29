-- Prove2me | Theorems.Thm_lean_workbook_plus_82018
-- name    : lean_workbook_plus_82018
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/ca0de6a3-c576-4152-a7b8-f4e5cc37c060
-- statement:
--   Prove that:\n$x^3(xy+xz-yz)(y-z)^2+y^3(xy+yz-zx)(z-x)^2+z^3(zx+yz-xy)(x-y)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82018 :  ∀ x y z : ℝ, x^3 * (x * y + x * z - y * z) * (y - z)^2 + y^3 * (x * y + y * z - z * x) * (z - x)^2 + z^3 * (z * x + y * z - x * y) * (x - y)^2 ≥ 0   :=  by sorry
