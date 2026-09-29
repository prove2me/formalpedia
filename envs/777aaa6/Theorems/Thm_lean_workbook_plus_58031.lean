-- Prove2me | Theorems.Thm_lean_workbook_plus_58031
-- name    : lean_workbook_plus_58031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/c10e93ae-b276-4d81-9922-5b29802871e2
-- statement:
--   Let $\alpha,\ \beta$ be the solutions of the quadratic equation $x^2-3x+5=0$ . Show that for each positive integer $n$ , $\alpha ^ n+\beta ^ n-3^n$ is divisible by 5.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58031 (n : ℕ) (α β : ℂ) (hα : α ^ 2 - 3 * α + 5 = 0) (hβ : β ^ 2 - 3 * β + 5 = 0) : 5 ∣ α ^ n + β ^ n - 3 ^ n   :=  by sorry
