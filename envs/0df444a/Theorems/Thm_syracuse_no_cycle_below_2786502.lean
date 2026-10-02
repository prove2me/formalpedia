-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_2786502
-- name    : syracuse_no_cycle_below_2786502
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-02T06:04:27.584687+00:00
-- url     : https://prove2.me/theorems/8b82562a-08bf-4b83-a7b3-36f0e888a07f
-- title:
--   No nontrivial Syracuse cycle state below 2786502
-- statement:
--   Let T(n) be the odd part of 3n+1, the accelerated Syracuse map. If m and p are natural numbers with m>0, p>0, m<2786502 and T^p(m)=m, then m=1. The return time need not be least and the starting state need not be the cycle minimum. This is a bounded cycle-state exclusion, not a claim that all Collatz trajectories converge or that every possible cycle has been excluded.
-- source:
--   Finite extension of the public Proved syracuse_no_cycle_below_2310000, https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 . Credits existing workspace CollatzFiniteDescent and CollatzFiniteDescentChunks checker/soundness modules, CollatzFiniteDescentExtensionChunk000 through047, CollatzFiniteDescentExtendedBand, CollatzCycleTools and CollatzCycleThreshold. Reuses the48 historical extension chunks covering odd states2307463 through2786501; exact new-band reindex is213284 and new count238251. A flattened source-only completed-proof candidate accompanies this draft. Historical checking is provenance, not new kernel acceptance or publication.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_no_cycle_below_2786502 (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hlt : m < 2786502) (hcyc : syracuseStep^[p] m = m) :
    m = 1 := by sorry
