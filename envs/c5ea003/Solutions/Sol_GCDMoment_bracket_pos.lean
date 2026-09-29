-- Prove2me | solution 1 for GCDMoment.bracket_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:09:30.001747+00:00
-- url     : https://prove2.me/submissions/cbc8afa1-44b0-4150-bdda-bc0f45f0dd0b

-- Sol generated from Novelty/GCDMomentPairInversion.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentTraceWitness

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

private lemma bracket_expand (p w n : ℤ) :
    (((2 + p) ^ 2 + (2 + p) * (3 + p + w) + (3 + p + w) ^ 2)
        * ((2 + p) ^ 2 + (2 + p) * (3 + p + w + n) + (3 + p + w + n) ^ 2) + (2 + p) ^ 2)
      + (85 + (88 * n + 11 * n ^ 2 + 176 * w + 86 * w * n + 8 * w * n ^ 2 + 86 * w ^ 2
        + 24 * w ^ 2 * n + w ^ 2 * n ^ 2 + 16 * w ^ 3 + 2 * w ^ 3 * n + w ^ 4 + 311 * p
        + 209 * p * n + 22 * p * n ^ 2 + 418 * p * w + 156 * p * w * n + 11 * p * w * n ^ 2
        + 156 * p * w ^ 2 + 33 * p * w ^ 2 * n + p * w ^ 2 * n ^ 2 + 22 * p * w ^ 3
        + 2 * p * w ^ 3 * n + p * w ^ 4 + 352 * p ^ 2 + 162 * p ^ 2 * n + 12 * p ^ 2 * n ^ 2
        + 324 * p ^ 2 * w + 81 * p ^ 2 * w * n + 3 * p ^ 2 * w * n ^ 2 + 81 * p ^ 2 * w ^ 2
        + 9 * p ^ 2 * w ^ 2 * n + 6 * p ^ 2 * w ^ 3 + 179 * p ^ 3 + 52 * p ^ 3 * n
        + 2 * p ^ 3 * n ^ 2 + 104 * p ^ 3 * w + 13 * p ^ 3 * w * n + 13 * p ^ 3 * w ^ 2
        + 43 * p ^ 4 + 6 * p ^ 4 * n + 12 * p ^ 4 * w + 4 * p ^ 5))
      = (2 + p) * (3 + p + w) * (3 + p + w + n) * ((2 + p) + (3 + p + w))
          * ((2 + p) + (3 + p + w + n)) := by
  ring









open GCDMoment in
theorem solution{a c d : ℤ} (ha : 2 ≤ a) (hac : a < c) (hcd : c ≤ d) :
    0 < a * c * d * (a + c) * (a + d) - (a ^ 2 + a * c + c ^ 2) * (a ^ 2 + a * d + d ^ 2)
      - a ^ 2 := by
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℤ, 0 ≤ p ∧ a = 2 + p := ⟨a - 2, by linarith, by ring⟩
  obtain ⟨w, hw, rfl⟩ : ∃ w : ℤ, 0 ≤ w ∧ c = 3 + p + w := ⟨c - 3 - p, by linarith, by ring⟩
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℤ, 0 ≤ n ∧ d = 3 + p + w + n :=
    ⟨d - 3 - p - w, by linarith, by ring⟩
  have h := bracket_expand p w n
  have hrest : (0 : ℤ) ≤ 88 * n + 11 * n ^ 2 + 176 * w + 86 * w * n + 8 * w * n ^ 2 + 86 * w ^ 2
      + 24 * w ^ 2 * n + w ^ 2 * n ^ 2 + 16 * w ^ 3 + 2 * w ^ 3 * n + w ^ 4 + 311 * p
      + 209 * p * n + 22 * p * n ^ 2 + 418 * p * w + 156 * p * w * n + 11 * p * w * n ^ 2
      + 156 * p * w ^ 2 + 33 * p * w ^ 2 * n + p * w ^ 2 * n ^ 2 + 22 * p * w ^ 3
      + 2 * p * w ^ 3 * n + p * w ^ 4 + 352 * p ^ 2 + 162 * p ^ 2 * n + 12 * p ^ 2 * n ^ 2
      + 324 * p ^ 2 * w + 81 * p ^ 2 * w * n + 3 * p ^ 2 * w * n ^ 2 + 81 * p ^ 2 * w ^ 2
      + 9 * p ^ 2 * w ^ 2 * n + 6 * p ^ 2 * w ^ 3 + 179 * p ^ 3 + 52 * p ^ 3 * n
      + 2 * p ^ 3 * n ^ 2 + 104 * p ^ 3 * w + 13 * p ^ 3 * w * n + 13 * p ^ 3 * w ^ 2
      + 43 * p ^ 4 + 6 * p ^ 4 * n + 12 * p ^ 4 * w + 4 * p ^ 5 := by positivity
  linarith
