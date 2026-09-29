-- Prove2me | Theorems.Thm_BinomialGCDA080170_not_pSq_dvd_central
-- name    : BinomialGCDA080170.not_pSq_dvd_central
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:05:28.665391+00:00
-- url     : https://prove2.me/theorems/64b58a0c-6032-4c3d-978b-9487298c28af
-- title:
--   Not pSq dvd central
-- statement:
--   Formal statement of `BinomialGCDA080170.not_pSq_dvd_central` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BinomialGCDA080170.not_pSq_dvd_central{p : ℕ} (hp : p.Prime) :
--       ¬ p ^ 2 ∣ Nat.choose (2 * (p - 1)) (p - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BinomialGCDA080170.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BinomialGCDA080170.lean#L117

-- Thm stub generated from Novelty/BinomialGCDA080170.lean
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

theorem BinomialGCDA080170.not_pSq_dvd_central{p : ℕ} (hp : p.Prime) :
    ¬ p ^ 2 ∣ Nat.choose (2 * (p - 1)) (p - 1) := by sorry
