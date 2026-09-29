-- Prove2me | Theorems.Thm_syracuse_descends_range_906576_908575
-- name    : syracuse_descends_range_906576_908575
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:05:20.987773+00:00
-- url     : https://prove2.me/theorems/74bf47fb-ecb9-44ca-9e52-b8fd26462c2e
-- title:
--   Syracuse descent for odd numbers between 906576 and 908575
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $906576 \le m \le 908575$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement rather than a convergence statement, which is the strength cycle exclusion needs: the minimum of a nontrivial cycle can never descend. Each orbit is followed only until its first drop below $906576$, and the residues $m \equiv 1 \pmod 4$ are handled uniformly, since $4 \mid 3m+1$ gives $T(m) \le (3m+1)/4 < m$ in one step.
--
--   This is a half-range, introduced because the combined range $[904575, 908575]$ exceeded the verifier's token-scanner budget even though it was within the source-size limit.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent half-range [906576, 908575], part of the ladder raising the cycle-minimum threshold from 860564 to 1166400.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_906576_908575 (m : ℕ) (hlo : 906576 ≤ m) (hhi : m ≤ 908575) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
