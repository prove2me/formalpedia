-- Prove2me | Theorems.Thm_lean_workbook_plus_850
-- name    : lean_workbook_plus_850
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8520985f-2f1f-4f6f-aa46-df9e5115f7b0
-- statement:
--   Now let $p=2$ . A necessary condition for $a^{2^n}- 1$ to be even is $a$ to be odd. Conversely, if $a$ is odd, then all factors (which are $n+1$ in amount) are even, so the whole product is divisible by $2^{n+1}$ (and in particular, by $2^n$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_850  (a n : ℕ)
  (h₀ : Odd a)
  : Even (a^(2^n) - 1)   :=  by sorry
