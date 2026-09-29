-- Prove2me | Theorems.Thm_lean_workbook_plus_2737
-- name    : lean_workbook_plus_2737
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7f8d7fbe-c1d4-4305-901d-d51896534923
-- statement:
--   Prove that $x^{4}+y^{4}+z^{4}+(x^{2}+y^{2}+z^{2})(xy+yz+zx) \ge 4(x^{2}y^{2}+y^{2}z^{2}+z^{2}x^{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2737 : ∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 + (x ^ 2 + y ^ 2 + z ^ 2) * (x * y + y * z + z * x) ≥ 4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)   :=  by sorry
