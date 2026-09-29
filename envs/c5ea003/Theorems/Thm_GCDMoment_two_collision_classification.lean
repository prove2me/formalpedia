-- Prove2me | Theorems.Thm_GCDMoment_two_collision_classification
-- name    : GCDMoment.two_collision_classification
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:56:43.763016+00:00
-- url     : https://prove2.me/theorems/a4ab5fe2-efcc-444f-8898-3f496c56e892
-- title:
--   Complete classification of the `k = 2` ambiguity.
-- statement:
--   **Complete classification of the `k = 2` ambiguity.**  `N = 28 = 2·14 = 4·7` and
--   `N = 36 = 2·18 = 3·12` are the *only* second-moment collisions, over all moduli: the collision
--   equation `a + b + c + d = N − 1` forces `N ≤ 36`, and a finite check finishes.
--
--   ```lean
--   theorem GCDMoment.two_collision_classification{a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
--       (hcd : c ≤ d) (hac : a < c) (hprod : a * b = c * d)
--       (hcoll : pairMoment 2 (a : ℤ) (b : ℤ) = pairMoment 2 (c : ℤ) (d : ℤ)) :
--       (a = 2 ∧ b = 14 ∧ c = 4 ∧ d = 7) ∨ (a = 2 ∧ b = 18 ∧ c = 3 ∧ d = 12) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/GCDMomentPairInversion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/GCDMomentPairInversion.lean#L91

-- Thm stub generated from Novelty/GCDMomentPairInversion.lean
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

theorem GCDMoment.two_collision_classification{a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hcd : c ≤ d) (hac : a < c) (hprod : a * b = c * d)
    (hcoll : pairMoment 2 (a : ℤ) (b : ℤ) = pairMoment 2 (c : ℤ) (d : ℤ)) :
    (a = 2 ∧ b = 14 ∧ c = 4 ∧ d = 7) ∨ (a = 2 ∧ b = 18 ∧ c = 3 ∧ d = 12) := by sorry
