-- Prove2me | Theorems.Thm_syracuse_descends_range_904575_906575
-- name    : syracuse_descends_range_904575_906575
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:05:51.728042+00:00
-- url     : https://prove2.me/theorems/524dd4b8-ee23-4984-bec4-0e6f46032ad9
-- title:
--   Syracuse descent for odd numbers between 904575 and 906575
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $904575 \le m \le 906575$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement rather than a convergence statement, which is the strength cycle exclusion needs: the minimum of a nontrivial cycle can never descend. Each orbit is followed only until its first drop below $904575$, and the residues $m \equiv 1 \pmod 4$ are handled uniformly, since $4 \mid 3m+1$ gives $T(m) \le (3m+1)/4 < m$ in one step.
--
--   This is a half-range, introduced because the combined range $[904575, 908575]$ exceeded the verifier's token-scanner budget even though it was within the source-size limit.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent half-range [904575, 906575], part of the ladder raising the cycle-minimum threshold from 860564 to 1166400.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_904575_906575 (m : ℕ) (hlo : 904575 ≤ m) (hhi : m ≤ 906575) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
