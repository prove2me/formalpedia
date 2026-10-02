-- Prove2me | Theorems.Thm_syracuse_cycle_repeated_valuation_word_le_6290_eq_one
-- name    : syracuse_cycle_repeated_valuation_word_le_6290_eq_one
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T17:56:48.393236+00:00
-- url     : https://prove2.me/theorems/9904e212-0ddd-46f3-b713-e4711ecc22fc
-- title:
--   Unbounded Syracuse return periods with valuation-word symmetry of shift at most 6290 are trivial
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$, and write $v_2$ for the exponent of two. Suppose $m,p,d\in\mathbb N$, $m>0$, $p>0$, and $T^p(m)=m$.
--
--   Assume the complete cyclic valuation word is invariant under a shift $d$ with $1\le d\le6290$: for every natural-number index $0\le i<p$,
--
--   $$v_2(3T^{i+d}(m)+1)=v_2(3T^i(m)+1).$$
--
--   Then
--
--   $$m=1.$$
--
--   The supplied return period $p$ and starting value $m$ are unbounded. The bound is on the word-symmetry shift $d$, not on $p$. No divisibility condition $d\mid p$ or least-period assumption is imposed. The comparison includes the cyclic boundary, not only a nonwrapping prefix.
--
--   This excludes an infinite restricted family of actual cycles. It does not exclude arbitrary primitive valuation words or prove the unbounded mission parent or Collatz conjecture.
-- source:
--   Collatz mission https://prove2.me/missions/Collatz_Conjecture . Structural consequence of the standard affine-word rigidity argument, composed with the public Proved syracuse_period_le_6290_eq_one (f0416d07-cb79-4120-a2dc-e83cc8fbcdd5), a coordinated consolidation of five existing period blocks. Uses syracuse_valuation_word_rotation_rigidity. Existing community period-exclusion and affine-prefix work are credited. No claim of globally novel mathematics or full primitive-word/tail exclusion.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_cycle_repeated_valuation_word_le_6290_eq_one (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p) (hd : 0 < d) (hdle : d ≤ 6290)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    m = 1 := by sorry
