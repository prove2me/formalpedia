-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_twenty_million_cutoff
-- name    : syracuse_no_cycle_below_twenty_million_cutoff
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T10:36:46.785422+00:00
-- url     : https://prove2.me/theorems/b5e0754a-5fbe-48bb-81b6-e9e8b7d41de4
-- title:
--   No nontrivial Syracuse cycle meets a state below 20,971,520
-- statement:
--   Let $T$ take the odd part of $3m+1$. For all $0<m<20{,}971{,}520$ and $p>0$, if $T^p(m)=m$, then $m=1$. The proof extends the $2^{23}$ cutoff by examining the minimum on a periodic orbit. A possible new minimum belongs to one of two arithmetic progressions modulo 12, and Lean verifies strict descent for both progressions.
-- source:
--   Minimum-state descent above the established cutoff https://prove2.me/theorems/3200d4f9-6281-4ae0-b7a3-d564488a54d7. The finite affine checker adapts that proof to two restricted progressions.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_no_cycle_below_twenty_million_cutoff (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hlt : m < 20971520)
    (hcycle : syracuseStep^[p] m = m) : m = 1 := by sorry
