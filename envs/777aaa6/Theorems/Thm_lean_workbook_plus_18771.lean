-- Prove2me | Theorems.Thm_lean_workbook_plus_18771
-- name    : lean_workbook_plus_18771
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/dade67ca-c627-4bc6-8059-64b0d4b517c4
-- statement:
--   prove that \n${\frac {1}{x \left( 1+x \right) \left( x+yz \right) }}+{\frac {1}{y\left( y+xz \right) \left( y+1 \right) }}+{\frac {1}{ \left( z+1 \right) z \left( z+xy \right) }}\geq 6\,{\frac {1}{ \left( xy+1 \right) \left( yz+1 \right) \left( xz+1 \right) }}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18771 : ∀ x y z : ℝ, (x * y + 1) * (y * z + 1) * (z * x + 1) ≠ 0 → 1 / (x * (1 + x) * (x + y * z)) + 1 / (y * (y + x * z) * (y + 1)) + 1 / ((z + 1) * z * (z + x * y)) ≥ 6 / ((x * y + 1) * (y * z + 1) * (z * x + 1))   :=  by sorry
