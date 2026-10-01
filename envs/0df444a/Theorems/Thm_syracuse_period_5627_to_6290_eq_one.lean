-- Prove2me | Theorems.Thm_syracuse_period_5627_to_6290_eq_one
-- name    : syracuse_period_5627_to_6290_eq_one
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T09:00:59.595983+00:00
-- url     : https://prove2.me/theorems/bf0c1a36-26ee-4698-b517-afe73d950254
-- title:
--   Syracuse cycles with return periods 5627 through 6290 are trivial
-- statement:
--   For the exact Syracuse map T(n), the odd part of 3n+1, every positive natural m with T^p(m)=m and 5627≤p≤6290 equals1. The return time need not be minimal. This excludes664 finite return periods for arbitrary starting values, not only bounded orbit representatives. It uses the existing public small-cycle exclusion below1883432 and threshold-parametrised cycle-margin criterion, together with a kernel-checkable exact-integer margin certificate. Period5626 and periods≥6291 are outside this statement.
-- source:
--   https://prove2.me/missions/Collatz_Conjecture; interval instantiation of syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_1883432 (33c2cf17-1597-4cb1-b85c-28dd910af0c9), following the public syracuse_period_4962_to_5625_eq_one method (2c64fcca-f85d-4bd9-843f-bca9a4259a58). Credit: Zexuan Liu's public margin pipeline and criterion work, and con's earlier interval instantiation. Arithmetic source: local Sol_collatz_cycle_margin_5627_6290.lean:11–143. This is an explicit certificate instantiation, not a new general cycle strategy or a theorem quoted verbatim from a paper.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

theorem syracuse_period_5627_to_6290_eq_one (m p : ℕ) (hm : 0 < m)
    (hlo : 5627 ≤ p) (hhi : p ≤ 6290) (hcyc : syracuseStep^[p] m = m) :
    m = 1 := by sorry
