-- Prove2me | solution 1 for GCDMoment.two_collision_classification
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:32:11.578112+00:00
-- url     : https://prove2.me/submissions/f2308c5d-c417-4175-aeae-c0038b973ec2

-- Sol generated from Novelty/GCDMomentPairInversion.lean
import Mathlib
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentTraceWitness
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

/-- At `k = 2` the predicted moment is a function of `N = ab` and the trace `a + b` alone. -/
theorem pairMoment_two_eq (a b : ℤ) :
    pairMoment 2 a b = (a * b) ^ 2 + 3 * (a * b) + 1 + (a * b - 1) * (a + b) - (a + b) ^ 2 := by
  rw [pairMoment]; ring

/-- **Exact collision law at `k = 2`.**  Two factorisations of the same modulus predict the same
second moment precisely when their traces agree or are complementary, `s + s' = N − 1`. -/
theorem pairMoment_two_collision_iff {a b c d : ℤ} (h : a * b = c * d) :
    pairMoment 2 a b = pairMoment 2 c d ↔ (a + b = c + d ∨ a + b + c + d = a * b - 1) := by
  rw [pairMoment_two_eq, pairMoment_two_eq, ← h]
  constructor
  · intro hEq
    have hfac : ((a + b) - (c + d)) * (a * b - 1 - (a + b) - (c + d)) = 0 := by linarith [hEq]
    rcases mul_eq_zero.1 hfac with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (h1 | h1)
    · linear_combination (a * b - 1 - (a + b) - (c + d)) * h1
    · linear_combination (c + d - a - b) * h1




/-! ### `k = 3`: strict monotonicity in the spread, and identifiability -/










open GCDMoment in
theorem solution{a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hcd : c ≤ d) (hac : a < c) (hprod : a * b = c * d)
    (hcoll : pairMoment 2 (a : ℤ) (b : ℤ) = pairMoment 2 (c : ℤ) (d : ℤ)) :
    (a = 2 ∧ b = 14 ∧ c = 4 ∧ d = 7) ∨ (a = 2 ∧ b = 18 ∧ c = 3 ∧ d = 12) := by
  have hprodZ : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hprod
  rcases (pairMoment_two_collision_iff hprodZ).1 hcoll with h1 | h1
  · exfalso
    have hsum : a + b = c + d := by exact_mod_cast h1
    obtain ⟨h2, -⟩ := sum_prod_determines_pair hprod hsum hab hcd
    omega
  · have hsum : a + b + c + d + 1 = a * b := by
      have h0 : ((a + b + c + d : ℕ) : ℤ) = (a : ℤ) * b - 1 := by push_cast at h1 ⊢; linarith
      have h2 : ((a + b + c + d : ℕ) : ℤ) + 1 = ((a * b : ℕ) : ℤ) := by
        push_cast at h0 ⊢; linarith
      exact_mod_cast h2
    have hc3 : 3 ≤ c := by omega
    have h1' : 2 * (a + b) ≤ 4 + a * b := by nlinarith
    have h2' : 3 * (c + d) ≤ 9 + c * d := by nlinarith
    have hN36 : a * b ≤ 36 := by omega
    have haa : a * a ≤ 36 := by nlinarith
    have ha6 : a ≤ 6 := by nlinarith
    have hcc : c * c ≤ 36 := by nlinarith
    have hc6 : c ≤ 6 := by nlinarith
    interval_cases a <;> interval_cases c <;> omega
