-- Prove2me | Theorems.Thm_lean_workbook_plus_47216
-- name    : lean_workbook_plus_47216
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/f904abfd-7647-4b09-a687-4dff0ad7e760
-- statement:
--   Consider the following expansion\n\n $ (x-a)(y-b)(z-b) \ge 0$ \n\n $ \Leftrightarrow xyz +xb^2+ab(y+z) \ge ab^2+ ayz + b(xy+xz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47216 (x y z a b : ℝ) : (x - a) * (y - b) * (z - b) ≥ 0 ↔ x * y * z + x * b ^ 2 + a * b * (y + z) ≥ a * b ^ 2 + a * y * z + b * (x * y + x * z)   :=  by sorry
