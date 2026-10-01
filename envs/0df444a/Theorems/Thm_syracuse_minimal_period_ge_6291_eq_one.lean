-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_6291_eq_one
-- name    : syracuse_minimal_period_ge_6291_eq_one
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-01T09:01:24.762712+00:00
-- url     : https://prove2.me/theorems/27c2e735-af66-4ff7-af77-9ac4694d59b1
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least 6291
-- statement:
--   Open remaining tail: if m>0 has least positive Syracuse return time p≥6291, prove m=1. Minimality means T^k(m)≠m for every0<k<p. This is the exact original cycle-frontier type with only its lower period bound raised. It does not claim the fixed5626 case or Collatz is solved.
-- source:
--   https://prove2.me/missions/Collatz_Conjecture; explicit unbounded tail child of syracuse_minimal_period_ge_5626_eq_one (1c671166-c069-4496-aee1-2f146072c8e5), after separating fixed5626 and the finite return-period block5627–6290. This node is an Open proof obligation.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

theorem syracuse_minimal_period_ge_6291_eq_one (m p : ℕ) (hm : 0 < m)
    (hp : 6291 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry
