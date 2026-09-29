-- Prove2me | Theorems.Thm_lean_workbook_plus_26556
-- name    : lean_workbook_plus_26556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/84de057a-d934-404b-9e62-d807f09e301f
-- statement:
--   Hence $ m^2 = 81$ . We have $ n^2\ge\frac {81}4\ge20$ and $ n^2 < \sqrt {1989}\le44$ . So $ n^2$ is either 25 or 36. Assume that $ n^2 = 25$ . Note that $ 25 - a,25 - b,25 - c$ are all nonnegative. We have $ (25 - a) + (25 - b) + (25 - c) = 19$ and $ (25 - a)^2 + (25 - b)^2 + (25 - c)^2 = 439$ . This is impossible since $ 19^2 < 439$ . So $ n^2 = 36$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26556  (m n a b c : ℤ)
  (h₀ : 0 < m ∧ 0 < n ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₁ : m^2 + n^2 + a^2 + b^2 + c^2 = 1989)
  (h₂ : m^2 + n^2 + a + b + c = 19)
  (h₃ : m^2 + a^2 + b^2 + c^2 = 44)
  (h₄ : n^2 + a^2 + b^2 + c^2 = 25) :
  m^2 = 81 ∧ n^2 = 36   :=  by sorry
