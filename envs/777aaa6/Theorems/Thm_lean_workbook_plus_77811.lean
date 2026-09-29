-- Prove2me | Theorems.Thm_lean_workbook_plus_77811
-- name    : lean_workbook_plus_77811
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6a0f500e-ac83-4ecd-a70f-445d25e4ae93
-- statement:
--   prove that \n $\left( 3\,xyz+{x}^{2}y+{y}^{2}z+{z}^{2}x \right) ^{2}\geq 4\,xyz \left( x\ny+zx+yz \right) \left( x+y+z \right) $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77811 : ∀ x y z : ℝ, (3 * x * y * z + x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ^ 2 ≥ 4 * x * y * z * (x * y + y * z + z * x) * (x + y + z)   :=  by sorry
