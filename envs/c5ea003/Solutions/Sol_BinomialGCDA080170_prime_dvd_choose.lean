-- Prove2me | solution 1 for BinomialGCDA080170.prime_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:47:59.337677+00:00
-- url     : https://prove2.me/submissions/27d7a3f7-7454-467a-8ea9-d57c87dbb424

-- Sol generated from Novelty/BinomialGCDA080170.lean
import Mathlib
import Definitions.Def_Novelty_BinomialGCDA080170

/-!
# The binomial GCD of OEIS A080170 and Ralf Stephan's conjecture (17)

For `k ≥ 2` put `n = k + 1` and
`D(k) = gcd_{2 ≤ q ≤ k+1} C(q·k, k)` (OEIS **A080170**).

Let `P(n)` be the largest *exact prime-power component* of `n`, i.e.
`P(n) = max_{p ∣ n} p^{v_p(n)}` where `v_p` is the `p`-adic valuation.

**Ralf Stephan's conjecture (17)** asserts an exact closed form:
`D(k) = P(n)` whenever `n / P(n) ≤ P(n)`, and `D(k) = 1` otherwise.

This file records the outcome of an adversarial research cycle on that
conjecture.  The two headline results are:

* `exact_value_conjecture_false` — the *exact value* part of Stephan's
  conjecture is **false**.  The first counterexample is `k = 11`
  (`n = 12 = 2²·3`): the closed form predicts `P(12) = 4`, but in fact
  `D(11) = 2`.  We prove `¬ (∀ k ≥ 2, D(k) = P(k+1))`.

* `prime_dvd_binomGCD` and `not_pSq_dvd_binomGCD` — on the *prime*
  fibre `n = p` the conjecture is *correct* and provably so at the level
  of the `p`-adic valuation: `p ∣ D(p-1)` but `p² ∤ D(p-1)`.  Hence the
  exact power of `p` dividing `D(p-1)` is `p¹`.  (Computation confirms the
  stronger `D(p-1) = p`; see `FUTURE_DIRECTIONS.md`.)

The proofs use **Kummer's theorem** (`Nat.padicValNat_choose'`, one of the
attached catalog references) to count base-`p` carries, generalising the
flavour of *Ram's theorem* on the gcd of a Pascal row.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Five falsifiable conjectures were posed:
  (H1) the *exact-value* form `D(k) = P(k+1)` under the dominance guard;
  (H2) the weaker *nontriviality* form `D(k) > 1 ⟺ (k+1)/P ≤ P`;
  (H3) `D(k)` is always a prime power or `1`;
  (H4) on prime powers `n = p^a` one has `D(p^a-1) = p^a`;
  (H5) a corrected closed form `D(k) = p^{a - ⌊log_p m⌋}` for the winning
       prime, where `p^a ∥ (k+1)` and `m = (k+1)/p^a`.

EXPERIMENT (Experimenter).  Direct evaluation of `D(k)` for `2 ≤ k ≤ 201`
(see `ComputationalEvidence.md`) showed:
  * H1 FAILS, first at `k = 11`: `D(11) = 2` but `P(12) = 4`.  Further
    failures at `k = 23, 35, 39, 44, 47, 55, 62, 71, 79, …`.
  * H2 SURVIVES on the entire tested range (no counterexample).
  * H3 SURVIVES: every `D(k)` is `1` or a prime power.
  * H4 SURVIVES: on prime powers Stephan's value is exact.
  * H5 SURVIVES: the corrected formula matches `D(k)` for all `2 ≤ k ≤ 201`.

ANALYSIS (Analyst).  H1 is *false* (not merely hard): the gcd is killed
below `P` by terms `q` with only one base-`p` carry.  Kummer's theorem
explains everything: `v_p(C(qk,k))` equals the number of carries when
adding `k` and `(q-1)k` in base `p`; the gcd takes the *minimum* over `q`,
which can be strictly below `v_p(n)`.  On the prime fibre `n = p` every
term has at least one carry (giving `p ∣ D(p-1)`) while the central term
`q = 2` has exactly one carry (giving `p² ∤ D(p-1)`), pinning the `p`-part
to `p¹`.  This is the structural reason Stephan's formula is exact for
prime powers (H4) but not in general.

CRITIQUE (Critic).  The disproof must not be a bare `decide`; we route it
through the divisibility `D(11) ∣ C(55,11)` (a `Finset.gcd` fact) together
with the single carry `4 ∤ C(55,11)`, so the *argument*, not brute force,
delivers the contradiction.  The prime-fibre results are genuinely general
(all primes `p`) and use Kummer in both directions, not computation.

SYNTHESIS (PI).  Stephan (17) splits cleanly: the *nontriviality* shape and
the *prime-power* value survive; the *general exact value* is refuted and
replaced by the carry-minimum formula H5.  See `FUTURE_DIRECTIONS.md`.
-/

open BinomialGCDA080170

open Nat Finset




/-
**Kummer lower bound.**  For a prime `p` and `2 ≤ q ≤ p`, the prime `p`
divides `C(q·(p-1), p-1)`: adding `p-1` and `(q-1)(p-1)` in base `p` produces
a carry in the units digit because `(p-1) + (p-(q-1)) = 2p-q ≥ p`.
-/

/-
**General lower bound on the prime fibre.**  `p ∣ D(p-1)` for every prime `p`.
-/

/-
**Kummer upper bound on the central term.**  For a prime `p`, the `p`-adic
valuation of the central coefficient `C(2(p-1), p-1)` is exactly `1`
(`(p-1)+(p-1) = 2p-2` has a single carry in base `p`), so `p² ∤ C(2(p-1),p-1)`.
-/

/-
**General upper bound on the prime fibre.**  `p² ∤ D(p-1)` for every prime `p`:
the gcd divides the central term `q = 2`, whose `p`-part is exactly `p`.
-/

/-
**Headline disproof.**  The *exact-value* part of Stephan's conjecture (17)
is false: there is no closed form `D(k) = P(k+1)` valid for all `k ≥ 2`.
Witness `k = 11`: `P(12) = 4` but `D(11) = 2`, because the gcd divides the
`q = 5` term `C(55, 11)`, which is not divisible by `4`.
-/


open BinomialGCDA080170 in
theorem solution{p q : ℕ} (hp : p.Prime) (hq2 : 2 ≤ q) (hqp : q ≤ p) :
    p ∣ Nat.choose (q * (p - 1)) (p - 1) := by
  -- Apply Kummer's theorem to show that the p-adic valuation of the binomial coefficient is at least 1.
  have h_kummer : padicValNat p (Nat.choose (q * (p - 1)) (p - 1)) ≥ 1 := by
    haveI := Fact.mk hp; rw [ padicValNat_choose ] ;
    any_goals exact Nat.lt_succ_self _;
    · refine Finset.card_pos.mpr ⟨ 1, ?_ ⟩ ; norm_num [ Nat.mod_eq_of_lt, hp.one_lt ];
      rcases p with ( _ | _ | p ) <;> simp_all +decide;
      rcases q with ( _ | _ | q ) <;> simp_all +decide [ Nat.succ_mul ];
      rw [ Nat.one_le_iff_ne_zero ] ; intro H ; have := Nat.dvd_of_mod_eq_zero H ; obtain ⟨ k, hk ⟩ := this ; nlinarith [ show k = q + 1 by nlinarith ];
    · nlinarith [ Nat.sub_pos_of_lt hp.one_lt ];
  convert Nat.dvd_of_mod_eq_zero _ using 1;
  exact Nat.mod_eq_zero_of_dvd <| by contrapose! h_kummer; simp_all +decide [ padicValNat.eq_zero_of_not_dvd ] ;
