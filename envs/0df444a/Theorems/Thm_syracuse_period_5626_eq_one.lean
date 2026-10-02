-- Prove2me | Theorems.Thm_syracuse_period_5626_eq_one
-- name    : syracuse_period_5626_eq_one
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T09:01:11.02828+00:00
-- url     : https://prove2.me/theorems/a5ccbe4c-fa79-4080-8bd2-8c80dc8a25e9
-- title:
--   Syracuse cycles with return period 5626 are trivial
-- statement:
--   Open supporting obligation: every positive natural m with T^5626(m)=m equals1. This stronger fixed-return statement does not require minimality and would cover the period5626 case of the active least-period≥5626 frontier. No proof of this claim or Collatz is asserted by publishing the problem.
-- source:
--   https://prove2.me/missions/Collatz_Conjecture; explicit remaining fixed-period case of syracuse_minimal_period_ge_5626_eq_one (1c671166-c069-4496-aee1-2f146072c8e5). This node is deliberately an Open proof obligation.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

theorem syracuse_period_5626_eq_one (m : ℕ) (hm : 0 < m)
    (hcyc : syracuseStep^[5626] m = m) :
    m = 1 := by sorry
