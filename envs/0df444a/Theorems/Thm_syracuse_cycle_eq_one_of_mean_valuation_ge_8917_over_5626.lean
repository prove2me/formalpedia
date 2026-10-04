-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_mean_valuation_ge_8917_over_5626
-- name    : syracuse_cycle_eq_one_of_mean_valuation_ge_8917_over_5626
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-02T15:36:48.290038+00:00
-- url     : https://prove2.me/theorems/a5875584-59dc-4703-bdba-f3d6f362bc7d
-- title:
--   High mean two-adic valuation at least 8917/5626 forces a positive Syracuse cycle to be one
-- statement:
--   Let T(n)=oddpart(3n+1). For arbitrary positive natural numbers m,p, suppose T^p(m)=m. Put K=sum_{i=0}^{p-1} v_2(3*T^i(m)+1). If 8917*p<=5626*K, then m=1.
--
--   The theorem covers the unbounded family of actual positive Syracuse cycles satisfying this high-mean condition. Its public type has no external baseline, margin, minimum-state, least-period, symmetry, divisibility-by-four, finite state bound or period-cap hypothesis. The proof imports the existing public Proved no-cycle-below-2310000 theorem, uses the effective four-window product threshold C=2786502 (not an orbit-state lower bound), and supplies the closed arithmetic certificate at exponent5626; that certificate does not require p=5626.
--
--   The strict complementary necessary condition for actual nontrivial cycles is 5626*K<8917*p. This new source packet has not been compiled, accepted or published. It does not assert that every possible cycle meets the high-mean condition, eliminate the remaining6291/9971 arithmetic pair, prove global word nondivisibility, exclude all cycles, close the unbounded tail or establish Collatz convergence.
-- source:
--   Unbounded high-mean cycle family assembled from the actual reviewed generic Task95 mathematical bodies, isolated in a fresh outer namespace. Discharges the global state threshold with the saved canonical public Proved syracuse_no_cycle_below_2310000 interface, UUID73735589-bbad-479f-8d7e-375fd2f82875, https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 . Uses the canonical Step Definition UUID2d5fcb43-85b2-4d75-beb8-3e236e66eac3. Copies the WHOLE two-part certificate from corrected fixed5626_v03 lines840-844 unchanged and transports its second component using the unchanged ordinary binaryPow helper. No generic95/prospective baseline theorem import; no acceptance transfers to the new source. Historical source reviews and the retained provenance finding are documented separately from this uncompiled/unreviewed packet. Public intent is explicit private=false data only, not publication or runtime approval.

import Mathlib
import Definitions.Def_syracuseStep
import Theorems.Thm_syracuse_no_cycle_below_2310000

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

open scoped BigOperators
universe u

theorem syracuse_cycle_eq_one_of_mean_valuation_ge_8917_over_5626 (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcyc : syracuseStep^[p] m = m)
    (hhigh : 8917 * p ≤ 5626 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2)) :
    m = 1 := by sorry
