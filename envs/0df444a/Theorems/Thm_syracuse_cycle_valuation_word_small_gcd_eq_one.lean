-- Prove2me | Theorems.Thm_syracuse_cycle_valuation_word_small_gcd_eq_one
-- name    : syracuse_cycle_valuation_word_small_gcd_eq_one
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T18:55:58.668345+00:00
-- url     : https://prove2.me/theorems/836cb62b-952d-4d24-9acd-e386db486b09
-- title:
--   Syracuse cycles with valuation-word symmetry and small period-shift gcd are trivial
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$, and let $v_2$ be the exponent of two. Write $T^k$ for $k$-fold iteration. Suppose $m,p,d\in\mathbb N$, $m>0$, $p>0$, and $T^p(m)=m$.
--
--   Assume the complete cyclic valuation word is invariant under the shift $d$: for every natural-number index $0\le i<p$,
--
--   $$v_2(3T^{i+d}(m)+1)=v_2(3T^i(m)+1).$$
--
--   If $\gcd(p,d)\le6290$, then
--
--   $$m=1.$$
--
--   Neither the supplied return period $p$ nor the shift $d$ is bounded; the bound is only on their greatest common divisor. No least-period, divisibility, or finite starting-value assumption is made. The comparison includes the cyclic return boundary, not just a nonwrapping prefix. The case $d=0$ is allowed and reduces to $p\le6290$.
--
--   This strengthens the short-shift word-symmetry criterion to a small-common-period criterion, including arbitrarily large coprime $p$ and $d$. It does not exclude arbitrary primitive valuation words, prove the unbounded mission parent, or establish Collatz convergence.
-- source:
--   Derived Collatz-mission corollary. Uses public Proved syracuse_valuation_word_rotation_rigidity https://prove2.me/theorems/9d080639-84a9-4f79-a536-21f43d096863 and the coordinated public Proved period-prefix consolidation syracuse_period_le_6290_eq_one https://prove2.me/theorems/f0416d07-cb79-4120-a2dc-e83cc8fbcdd5 . The intervening gcd-period fact is the standard Mathlib Function.IsPeriodicPt.gcd theorem, pinned Mathlib/Dynamics/PeriodicPts/Defs.lean:157–163. Generalizes the existing short-shift corollary https://prove2.me/theorems/9904e212-0ddd-46f3-b713-e4711ecc22fc . Credits existing community cycle exclusions and the earlier affine-word rigidity formalization. No globally novel mathematics or complete primitive-word/tail exclusion claimed.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_cycle_valuation_word_small_gcd_eq_one (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hg : Nat.gcd p d ≤ 6290)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    m = 1 := by sorry
