-- Prove2me | Theorems.Thm_syracuse_valuation_word_rotation_rigidity
-- name    : syracuse_valuation_word_rotation_rigidity
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T17:23:57.434992+00:00
-- url     : https://prove2.me/theorems/9d080639-84a9-4f79-a536-21f43d096863
-- title:
--   A cyclic Syracuse valuation-word symmetry forces a return
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$ and let $v_2$ denote the exponent of two. Suppose $m,p,d\in\mathbb N$, $m>0$, $p>0$, and $T^p(m)=m$.
--
--   If the following equality holds for every natural-number index $0\le i<p$,
--
--   $$v_2(3T^{i+d}(m)+1)=v_2(3T^i(m)+1),$$
--
--   then
--
--   $$T^d(m)=m.$$
--
--   This compares the whole cyclic valuation word, including the return boundary, not a shorter nonwrapping prefix. There is no upper bound on $m,p,d$ and no least-period or finite-state-threshold hypothesis.
--
--   The result supplies structural rigidity valid for unbounded periods. It does not exclude arbitrary primitive cycle words or prove the unbounded mission parent.
-- source:
--   Collatz mission https://prove2.me/missions/Collatz_Conjecture . Standard affine valuation-word telescoping/uniqueness argument, using the public cycle power-gap theorem syracuse_cycle_pow_two_gt_pow_three (955877f3-88bd-4837-b1d9-2e4467430637). Community baseline/power-gap work is credited; this formalization does not claim globally novel mathematics or full tail closure. Related existing affine-prefix congruence work: syracuse_valuation_prefix_residue (97b3505f-d519-4267-91cc-4b5834a4c5be), formalized by mysticflounder following Tao’s deterministic residue argument. The present exact periodic-equality result is distinct; that source is credited for related context, not imported or copied.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_valuation_word_rotation_rigidity (m p d : ℕ)
    (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hword : ∀ i : ℕ, i < p →
      (3 * syracuseStep^[i + d] m + 1).factorization 2 =
        (3 * syracuseStep^[i] m + 1).factorization 2) :
    syracuseStep^[d] m = m := by sorry
