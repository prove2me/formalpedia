-- Prove2me | Theorems.Thm_lean_workbook_plus_27984
-- name    : lean_workbook_plus_27984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3f96adde-f95c-4fbf-865c-a53a4189a4bc
-- statement:
--   The remaining $n - m$ teams play $\binom{n - m}{2}$ games among themselves, for a total of $(n-m)(n-m-1)$ points. Again this represents half of the sum of their total points, so their total points is $2(n-m)(n-m-1) = 2(n^2 - 2mn + m^2 - n + m) = 2n^2 - 4mn + 2m^2 - 2n + 2m.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27984  (n m : ℕ)
  (h₀ : n > m)
  (h₁ : 0 < m) :
  2 * (n^2 - 2 * n * m + m^2 - n + m) = 2 * n^2 - 4 * n * m + 2 * m^2 - 2 * n + 2 * m   :=  by sorry
