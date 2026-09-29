-- Prove2me | Theorems.Thm_lean_workbook_plus_54144
-- name    : lean_workbook_plus_54144
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/b297f008-5ced-41df-b12a-52039f030fa7
-- statement:
--   Let $ x, y, z > 0$ . Prove that the following inequality holds: $ \frac {x^2 + y^2 + z^2}{xy + yz + zx}\geq 1 + \left(\frac {x + y}{z} + \frac {z + x}{y} + \frac {y + z}{x}\right) - 4\left(\frac {x}{y + z} + \frac {y}{z + x} + \frac {z}{x + y}\right).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54144 :  ∀ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 → (x^2 + y^2 + z^2) / (x * y + y * z + z * x) ≥ 1 + (x + y) / z + (z + x) / y + (y + z) / x - 4 * (x / (y + z) + y / (z + x) + z / (x + y))   :=  by sorry
