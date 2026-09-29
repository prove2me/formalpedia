-- Prove2me | Theorems.Thm_lean_workbook_plus_75775
-- name    : lean_workbook_plus_75775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e0bd6f02-d6e4-45ce-ba8f-8ff4110d2c87
-- statement:
--   prove that: $x^4y^2+y^4z^2+z^4x^2 \geq \frac{1}{4}(yz(x^2+yz)(y^2+xz)+zx(y^2+xz)(z^2+xy)+xy(z^2+xy)(x^2+yz))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75775 :  ∀ x y z : ℝ, x ^ 4 * y ^ 2 + y ^ 4 * z ^ 2 + z ^ 4 * x ^ 2 ≥  1 / 4 * (y * z * (x ^ 2 + y * z) * (y ^ 2 + x * z) + z * x * (y ^ 2 + x * z) * (z ^ 2 + x * y) + x * y * (z ^ 2 + x * y) * (x ^ 2 + y * z))   :=  by sorry
