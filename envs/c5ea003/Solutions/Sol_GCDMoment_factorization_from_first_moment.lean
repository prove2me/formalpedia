-- Prove2me | solution 1 for GCDMoment.factorization_from_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:32:10.56592+00:00
-- url     : https://prove2.me/submissions/f1940836-eb96-4e41-91a2-a6e65289e1f2

-- Sol generated from Novelty/GCDMomentPairInversion.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Theorems.Thm_GCDMoment_pairMoment_eq_gcdMoment
import Theorems.Thm_GCDMoment_sum_prod_determines_pair

/-!
# Inverting the gcd moments: which moment identifies the factorisation?

Companion to `Novelty.GCDMomentTraceWitness`.  There the gcd moment of a semiprime was shown
to be a polynomial `F_k(N, s)` in the modulus `N = pq` and the trace `s = p + q`.  Here we
study the *inversion problem* an adversary actually faces:

> given the modulus `N` and the observed value of the `k`-th gcd moment, how many candidate
> factorisations `N = a·b` (`2 ≤ a ≤ b`) reproduce that value?

For a candidate pair `(a,b)` the predicted moment is
`pairMoment k a b = a^k(b−1) + b^k(a−1) + (a−1)(b−1) + (ab)^k`, which for a genuine prime pair
agrees with `gcdMoment k (p*q)` (`pairMoment_eq_gcdMoment`).

## Main results

* `pairMoment_two_eq` — at `k = 2` the prediction depends on the pair only through `N` and the
  trace `a + b`.
* `pairMoment_two_collision_iff` — **exact collision law at `k = 2`**: two factorisations of the
  same `N` give the same second moment iff they have the same trace or *complementary* traces,
  `(a+b) + (c+d) = N − 1`.  This is the `s ↦ N − 1 − s` symmetry of the moment polynomial,
  now visible on genuine factorisations.
* `pairMoment_two_collision_28`, `pairMoment_two_collision_36` — the collision is not vacuous:
  `28 = 2·14 = 4·7` and `36 = 2·18 = 3·12` are honest counterexamples to identifiability
  at `k = 2`.
* `two_collision_classification` — **and these two are the only ones, over all moduli**: the
  collision equation forces `N ≤ 36`, after which a finite check finishes.
* `bracket_pos`, `pairMoment_three_identity`, `pairMoment_three_spread_strict` — **the third
  moment is strictly monotone in the spread of the factorisation**: if `a < c ≤ d < b` and
  `ab = cd`, then `pairMoment 3 c d < pairMoment 3 a b`.
* `pairMoment_three_injective` — consequently the third moment *does* identify the
  factorisation: no two distinct factorisations of the same `N` share a third moment.
  The `k = 2` ambiguity disappears at `k = 3`, with no size cut needed.
* `gcdMoment_three_identifies_factors` — the arithmetic payoff: for a semiprime `N = pq`, the
  observed third gcd moment singles out `(p,q)` among *all* nontrivial factorisations.

The contrast `k = 2` (ambiguous, needs the size cut `2s < N − 1`) versus `k = 3` (unambiguous)
is the correct form of the informal "root ambiguity" question: the ambiguity is real at `k = 2`
and disappears at `k = 3`, while the *cost* of computing the moment (Ω(N) gcds, and a variance
that grows like `N^{2k−1}`) only gets worse — which is why no member of the family factors.
-/

open GCDMoment



/-! ### `k = 2`: the collision law -/






/-! ### `k = 3`: strict monotonicity in the spread, and identifiability -/










open GCDMoment in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    {a b : ℕ} (hab : a ≤ b) (hprod : a * b = p * q)
    (hmatch : pairMoment 1 (a : ℤ) (b : ℤ) = (gcdMoment 1 (p * q) : ℤ)) : a = p ∧ b = q := by
  have htrue : pairMoment 1 (p : ℤ) (q : ℤ) = (gcdMoment 1 (p * q) : ℤ) :=
    pairMoment_eq_gcdMoment hp hq (by omega) 1
  have hcoll : pairMoment 1 (a : ℤ) (b : ℤ) = pairMoment 1 (p : ℤ) (q : ℤ) := by
    rw [hmatch, htrue]
  have hprodZ : (a : ℤ) * b = (p : ℤ) * q := by exact_mod_cast hprod
  have hsumZ : (a : ℤ) + b = (p : ℤ) + q := by
    simp only [pairMoment, pow_one] at hcoll
    nlinarith [hcoll, hprodZ]
  have hsum : a + b = p + q := by exact_mod_cast hsumZ
  exact sum_prod_determines_pair hprod hsum hab (le_of_lt hpq)
