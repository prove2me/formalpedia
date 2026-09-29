-- Prove2me | Theorems.Thm_lean_workbook_plus_41493
-- name    : lean_workbook_plus_41493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4b31808b-a416-4bbd-a038-c8e3f67ac438
-- statement:
--   Let $ \begin {cases} x+y+z=5\xy+yz+zx=8 \end{cases}$ . Prove that $ 1\le x \le \frac{7}{3}$ ; $ 1\le y \le \frac{7}{3}$ ; $ 1\le z \le \frac{7}{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41493 {x y z : ℝ} (hx : x + y + z = 5) (hy : x * y + y * z + z * x = 8) : 1 ≤ x ∧ x ≤ 7 / 3 ∧ 1 ≤ y ∧ y ≤ 7 / 3 ∧ 1 ≤ z ∧ z ≤ 7 / 3   :=  by sorry
