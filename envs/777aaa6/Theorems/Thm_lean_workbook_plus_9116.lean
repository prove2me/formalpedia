-- Prove2me | Theorems.Thm_lean_workbook_plus_9116
-- name    : lean_workbook_plus_9116
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/98f33503-e2d6-498d-8f04-5b370775e34d
-- statement:
--   and so, we only need to prove \n $ 6(x + y + z)^2 \ge 5\sum x^2 + 13\sum xy,$ which is equivalent to $ x^2 + y^2 + z^2 \ge xy + yz + zx$ (trivial).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9116 :
  ∀ x y z : ℝ, 6 * (x + y + z) ^ 2 ≥ 5 * (x ^ 2 + y ^ 2 + z ^ 2) + 13 * (x * y + y * z + z * x)   :=  by sorry
