-- Prove2me | solution 1 for lean_workbook_plus_68985
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:26.537779+00:00
-- url     : https://prove2.me/submissions/82a78615-ae10-4612-8504-845a94117c04

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c d : ℝ) (hab : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0)
    (habc : a ^ 2 + b ^ 2 + (a - b) ^ 2 = c ^ 2 + d ^ 2 + (c - d) ^ 2) :
    a ^ 4 + b ^ 4 + (a - b) ^ 4 = c ^ 4 + d ^ 4 + (c - d) ^ 4 := by
  have hs := congrArg (fun t : ℝ => t ^ 2) habc
  nlinarith [hs]
