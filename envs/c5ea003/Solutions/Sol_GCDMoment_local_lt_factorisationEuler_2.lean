-- Prove2me | solution 2 for GCDMoment.local_lt_factorisationEuler
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:40:56.606985+00:00
-- url     : https://prove2.me/submissions/2253f43a-486f-41ef-a965-f60636159fa6

import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentRefinementOrder
import Definitions.Def_Novelty_GCDMomentTraceWitness

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Novelty/GCDMomentTraceWitness.lean ====
/-!
# GCD moments of a semiprime: a closed trace-witness family

For a positive integer `n` and an exponent `k` put

`M_k(n) = ∑_{x < n} gcd(n, x) ^ k`

(the sum over a full residue system; the term `x = 0` contributes `n ^ k`, which is the same
as the term `x = n` in the more usual range `1 ≤ x ≤ n`).

This file develops the arithmetic of these *gcd moments* for a **semiprime** `N = p * q`
(`p`, `q` distinct primes), the setting of the factoring-barrier catalog.  Writing
`s = p + q` for the *trace*, the results are as follows.

## Main results

* `gcdMoment_eq_sum_divisors` — the classical gcd-sum / Jordan-totient identity
  `M_k(n) = ∑_{d ∣ n} d^k φ(n/d)`, valid for every `n > 0`.
* `newtonP_eq` — the Newton recursion `P_{j+2} = s P_{j+1} − N P_j` computes the power sums
  `P_j = p^j + q^j` from the pair `(N, s)` alone.
* `gcdMoment_semiprime_four_terms` and `gcdMoment_eq_momentPoly` — **the closed form**: for
  `k ≥ 1`, `M_k(N) = N^k + N·P_{k−1} − P_k + N − s + 1 = F_k(N, s)`, an explicit integer
  polynomial in the *public* modulus `N` and the trace `s`.  This is the symmetry barrier:
  the individual factors never appear, only their elementary symmetric functions.
* `gcdMoment_one`, `gcdMoment_two`, `gcdMoment_three`, `gcdMoment_four` — the explicit
  low-order polynomials, e.g. `M_1 = 4N − 2s + 1` and `M_2 = N² + 3N + 1 + (N−1)s − s²`.
* `trace_of_gcdMoment_one` — the first moment recovers the trace exactly: `2 s = 4N + 1 − M_1`.
* `higher_moments_from_first` — **closure of the family**: every higher moment is an explicit
  function of `N` and `M_1`.  No moment carries information beyond the trace.
* `sum_prod_determines_pair`, `discriminant_eq` and `factorization_of_gcdMoment_one` — the
  trace *does* split `N`: the pair `(p,q)` is the unique ordered pair of naturals with the
  observed product and trace, and the discriminant `s² − 4N = (q−p)²` is a perfect square.
  So `M_1` is a complete witness — but computing it costs `Θ(N)` gcds.
* `momentPoly_two_symm`, `momentPoly_two_root_dichotomy`, `trace_unique_of_small` — the
  `k = 2` moment polynomial has exactly the two roots `s` and `N − 1 − s`, and the size cut
  `2s < N − 1` picks out the true trace.  (The second root is not a phantom: the companion file
  `Novelty.GCDMomentPairInversion` exhibits moduli where it is realised by a genuine second
  factorisation, and shows there are exactly two such moduli.)
* `gcdMoment_ge`, `gcdMoment_le`, `gcdVariance_lower_bound`, `gcdVariance_upper_bound`,
  `gcdVariance_theta`, `gcdVariance_one_le`, `gcdVariance_separation` — the *cost* hierarchy.  The variance of `gcd(N,U)^k` for uniform
  `U` is at least `N^{2k−1} − 16 N^{2k−2}`, while for `k = 1` it is at most `4N`; hence
  Chebyshev sampling at level `k` needs `Ω(N^{2k−1})` samples and `k = 1` is optimal.
* `card_nontrivial_gcd` — the witness-density law `#{x < N : gcd(N,x) ≠ 1} = p + q − 1`:
  a uniform probe hits a nontrivial gcd with probability exactly `(p+q−1)/N`, the `Θ(p+q)`
  query threshold.

Nothing here breaks the factoring barrier: every statement is either an identity in `(N, s)`
or an `Ω(N)`-cost computation.
-/

namespace GCDMoment

open Finset Nat

/-! ### Definition and the divisor form -/

-- [dropped: platform already declares gcdMoment]
@[simp] lemma gcdMoment_zero_right (k : ℕ) : gcdMoment k 0 = 0 := by simp [gcdMoment]

/-- Sanity checks against the closed forms below (`N = 6`, `s = 5`; `N = 15`, `s = 8`). -/
example : gcdMoment 1 6 = 15 := by decide
example : gcdMoment 2 6 = 55 := by decide
example : gcdMoment 1 15 = 4 * 15 - 2 * 8 + 1 := by decide

/-- The classical gcd-sum / Jordan-totient identity `∑_{x<n} gcd(n,x)^k = ∑_{d ∣ n} d^k φ(n/d)`. -/
theorem gcdMoment_eq_sum_divisors (k n : ℕ) (hn : 0 < n) :
    gcdMoment k n = ∑ d ∈ n.divisors, d ^ k * φ (n / d) := by
  unfold gcdMoment
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => n.gcd x) (t := n.divisors)
      (fun x _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
  simp [mul_comm]

/-- The divisors of a semiprime are `1, p, q, pq`. -/
theorem divisors_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {1, p, q, p * q} := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, -⟩
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      rcases (Nat.dvd_prime hq).1 ((mul_dvd_mul_iff_left hp.pos.ne').1 hd) with rfl | rfl
      · simp
      · simp
    · have hcop : Nat.Coprime d p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd)
      rcases (Nat.dvd_prime hq).1 (hcop.dvd_of_dvd_mul_left hd) with rfl | rfl
      · simp
      · simp
  · rintro (rfl | rfl | rfl | rfl) <;>
      simp [Dvd.intro, hp.ne_zero, Nat.mul_ne_zero hp.ne_zero hq.ne_zero]

/-- The four-term expansion of the gcd moment of a semiprime, over `ℤ`. -/
theorem gcdMoment_semiprime_four_terms {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k : ℕ) :
    (gcdMoment k (p * q) : ℤ) =
      ((p : ℤ) - 1) * ((q : ℤ) - 1) + (p : ℤ) ^ k * ((q : ℤ) - 1)
        + (q : ℤ) ^ k * ((p : ℤ) - 1) + ((p : ℤ) * (q : ℤ)) ^ k := by
  have hN : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  rw [gcdMoment_eq_sum_divisors k _ hN]
  have h1p : (1 : ℕ) ≠ p := hp.one_lt.ne
  have h1q : (1 : ℕ) ≠ q := hq.one_lt.ne
  have h1pq : (1 : ℕ) ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have hppq : p ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  have hqpq : q ≠ p * q := by nlinarith [hp.one_lt, hq.one_lt]
  rw [divisors_semiprime hp hq, Finset.sum_insert (by simp [h1p, h1q, h1pq]),
    Finset.sum_insert (by simp [hpq, hppq]), Finset.sum_insert (by simp [hqpq]),
    Finset.sum_singleton]
  have e2 : (p * q) / p = q := Nat.mul_div_cancel_left q hp.pos
  have e3 : (p * q) / q = p := by rw [mul_comm]; exact Nat.mul_div_cancel_left p hq.pos
  have e4 : (p * q) / (p * q) = 1 := Nat.div_self hN
  rw [Nat.div_one, e2, e3, e4, Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq),
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_one]
  push_cast [Nat.cast_sub hp.one_lt.le, Nat.cast_sub hq.one_lt.le]
  ring

/-! ### Newton power sums and the moment polynomial -/

/-- The Newton power sums `P_j` as a polynomial recursion in the public data `(N, s)`:
`P_0 = 2`, `P_1 = s`, `P_{j+2} = s P_{j+1} − N P_j`. -/
-- [dropped: platform already declares newtonP]
@[simp] lemma newtonP_zero (N s : ℤ) : newtonP N s 0 = 2 := rfl
@[simp] lemma newtonP_one (N s : ℤ) : newtonP N s 1 = s := rfl
lemma newtonP_succ_succ (N s : ℤ) (j : ℕ) :
    newtonP N s (j + 2) = s * newtonP N s (j + 1) - N * newtonP N s j := rfl

/-- The recursion really computes the power sums `p^j + q^j` from `(pq, p+q)` alone. -/
theorem newtonP_eq (p q : ℤ) (j : ℕ) : newtonP (p * q) (p + q) j = p ^ j + q ^ j := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more j ih1 ih2 => rw [newtonP_succ_succ, ih1, ih2]; ring

/-- `momentPoly N s k = F_{k+1}(N,s)`, the closed form of the `(k+1)`-st gcd moment. -/
-- [dropped: platform already declares momentPoly]
theorem gcdMoment_eq_momentPoly {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ) :
    (gcdMoment (k + 1) (p * q) : ℤ) = momentPoly ((p : ℤ) * q) ((p : ℤ) + q) k := by
  rw [gcdMoment_semiprime_four_terms hp hq hpq, momentPoly, newtonP_eq, newtonP_eq]
  ring

/-- Barrier 2 in its bare form: the moments are invariant under any change of the hidden pair
that preserves the product and the trace. -/
theorem gcdMoment_eq_of_same_trace {p q p' q' : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp' : p'.Prime) (hq' : q'.Prime) (hpq' : p' ≠ q')
    (hprod : (p : ℤ) * q = (p' : ℤ) * q') (htr : (p : ℤ) + q = (p' : ℤ) + q') (k : ℕ) :
    (gcdMoment (k + 1) (p * q) : ℤ) = (gcdMoment (k + 1) (p' * q') : ℤ) := by
  rw [gcdMoment_eq_momentPoly hp hq hpq, gcdMoment_eq_momentPoly hp' hq' hpq', hprod, htr]

/-! ### The explicit low moments -/

theorem momentPoly_zero (N s : ℤ) : momentPoly N s 0 = 4 * N - 2 * s + 1 := by
  simp [momentPoly]; ring

theorem momentPoly_one (N s : ℤ) : momentPoly N s 1 = N ^ 2 + 3 * N + 1 + (N - 1) * s - s ^ 2 := by
  simp [momentPoly, newtonP_succ_succ]; ring

theorem momentPoly_two (N s : ℤ) :
    momentPoly N s 2 = N ^ 3 - 2 * N ^ 2 + N * s ^ 2 + 3 * N * s + N - s ^ 3 - s + 1 := by
  simp [momentPoly, newtonP_succ_succ]; ring

theorem momentPoly_three (N s : ℤ) :
    momentPoly N s 3 =
      N ^ 4 - 3 * N ^ 2 * s - 2 * N ^ 2 + N * s ^ 3 + 4 * N * s ^ 2 + N - s ^ 4 - s + 1 := by
  simp [momentPoly, newtonP_succ_succ]; ring

variable {p q : ℕ}

theorem gcdMoment_one (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gcdMoment 1 (p * q) : ℤ) = 4 * ((p : ℤ) * q) - 2 * ((p : ℤ) + q) + 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, gcdMoment_eq_momentPoly hp hq hpq, momentPoly_zero]

theorem gcdMoment_two (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gcdMoment 2 (p * q) : ℤ) =
      ((p : ℤ) * q) ^ 2 + 3 * ((p : ℤ) * q) + 1 + ((p : ℤ) * q - 1) * ((p : ℤ) + q)
        - ((p : ℤ) + q) ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, gcdMoment_eq_momentPoly hp hq hpq, momentPoly_one]

theorem gcdMoment_three (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gcdMoment 3 (p * q) : ℤ) =
      ((p : ℤ) * q) ^ 3 - 2 * ((p : ℤ) * q) ^ 2 + ((p : ℤ) * q) * ((p : ℤ) + q) ^ 2
        + 3 * ((p : ℤ) * q) * ((p : ℤ) + q) + ((p : ℤ) * q) - ((p : ℤ) + q) ^ 3
        - ((p : ℤ) + q) + 1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, gcdMoment_eq_momentPoly hp hq hpq, momentPoly_two]

theorem gcdMoment_four (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (gcdMoment 4 (p * q) : ℤ) =
      ((p : ℤ) * q) ^ 4 - 3 * ((p : ℤ) * q) ^ 2 * ((p : ℤ) + q) - 2 * ((p : ℤ) * q) ^ 2
        + ((p : ℤ) * q) * ((p : ℤ) + q) ^ 3 + 4 * ((p : ℤ) * q) * ((p : ℤ) + q) ^ 2
        + ((p : ℤ) * q) - ((p : ℤ) + q) ^ 4 - ((p : ℤ) + q) + 1 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, gcdMoment_eq_momentPoly hp hq hpq, momentPoly_three]

/-! ### Trace recovery and closure of the family -/

/-- **Trace recovery.**  The first gcd moment determines the trace `s = p + q` exactly. -/
theorem trace_of_gcdMoment_one (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    2 * ((p : ℤ) + q) = 4 * ((p : ℤ) * q) + 1 - gcdMoment 1 (p * q) := by
  rw [gcdMoment_one hp hq hpq]; ring

/-- **Closure of the moment family (barriers 6 and 8).**  Every higher gcd moment is an explicit
polynomial function of the modulus and of the *first* moment: the family carries exactly one
bit of hidden information, the trace, and higher `k` adds nothing. -/
theorem higher_moments_from_first (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ) {s : ℤ}
    (hs : 2 * s = 4 * ((p : ℤ) * q) + 1 - gcdMoment 1 (p * q)) :
    (gcdMoment (k + 1) (p * q) : ℤ) = momentPoly ((p : ℤ) * q) s k := by
  have : s = (p : ℤ) + q := by
    have := trace_of_gcdMoment_one hp hq hpq
    omega
  rw [this, gcdMoment_eq_momentPoly hp hq hpq]

/-! ### The `k = 2` root structure -/

/-- The second moment polynomial is symmetric about `s ↦ N − 1 − s`. -/
theorem momentPoly_two_symm (N s : ℤ) : momentPoly N (N - 1 - s) 1 = momentPoly N s 1 := by
  rw [momentPoly_one, momentPoly_one]; ring

/-- The second moment pins the trace down to exactly two candidates. -/
theorem momentPoly_two_root_dichotomy {N s t : ℤ} (h : momentPoly N t 1 = momentPoly N s 1) :
    t = s ∨ t = N - 1 - s := by
  rw [momentPoly_one, momentPoly_one] at h
  have h' : (t - s) * (N - 1 - t - s) = 0 := by linarith [h, sq_nonneg (t - s)]
  rcases mul_eq_zero.1 h' with h1 | h1
  · left; linarith
  · right; linarith

/-- **The size cut disambiguates.**  Among candidate traces below `(N−1)/2` the second moment
determines the trace uniquely. -/
theorem trace_unique_of_small {N s t : ℤ} (hs : 2 * s < N - 1) (ht : 2 * t < N - 1)
    (h : momentPoly N t 1 = momentPoly N s 1) : t = s := by
  rcases momentPoly_two_root_dichotomy h with h1 | h1
  · exact h1
  · exfalso; omega

/-! ### The trace splits `N` -/

/-- A pair of naturals is determined by its sum and product (up to order). -/
theorem sum_prod_determines_pair {a b c d : ℕ} (hprod : a * b = c * d) (hsum : a + b = c + d)
    (hab : a ≤ b) (hcd : c ≤ d) : a = c ∧ b = d := by
  have hprodZ : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hprod
  have hsumZ : (a : ℤ) + b = (c : ℤ) + d := by exact_mod_cast hsum
  have key : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by nlinarith [hprodZ, hsumZ]
  rcases mul_eq_zero.1 key with h | h
  · have hac : a = c := by exact_mod_cast sub_eq_zero.1 h
    exact ⟨hac, by omega⟩
  · have had : a = d := by exact_mod_cast sub_eq_zero.1 h
    have : c = d := by omega
    exact ⟨by omega, by omega⟩

/-- The discriminant of the trace quadratic is the square of the gap between the factors. -/
theorem discriminant_eq (p q : ℕ) :
    ((p : ℤ) + q) ^ 2 - 4 * ((p : ℤ) * q) = ((q : ℤ) - p) ^ 2 := by ring

/-- **The gcd-sum witness is complete.**  Any ordered pair `(a,b)` of naturals whose product is
`N` and whose sum is the trace read off from the first gcd moment *is* the factorisation.
Thus an `O(N)` gcd scan factors `N` — the witness is genuine, but its cost is `Θ(N)`. -/
theorem factorization_of_gcdMoment_one (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hle : p ≤ q)
    {a b : ℕ} (hab : a ≤ b) (hprod : a * b = p * q)
    (hsum : 2 * ((a : ℤ) + b) = 4 * ((p : ℤ) * q) + 1 - gcdMoment 1 (p * q)) :
    a = p ∧ b = q := by
  have htr := trace_of_gcdMoment_one hp hq hpq
  have hsum' : a + b = p + q := by
    have : ((a : ℤ) + b) = (p : ℤ) + q := by omega
    exact_mod_cast this
  exact sum_prod_determines_pair hprod hsum' hab hle

/-! ### The cost hierarchy: variance of the `k`-th gcd power -/

/-- Every gcd moment is at least `N^k`: the single probe `x ≡ 0` already contributes `N^k`. -/
theorem gcdMoment_ge (k n : ℕ) (hn : 0 < n) : n ^ k ≤ gcdMoment k n := by
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.2 hn
  have := Finset.single_le_sum (f := fun x => (n.gcd x) ^ k) (fun i _ => Nat.zero_le _) h0
  simpa using this

/-- Conversely every gcd moment of a semiprime is at most `4 N^k` (`k ≥ 1`). -/
theorem gcdMoment_le (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    (gcdMoment (j + 1) (p * q) : ℤ) ≤ 4 * ((p : ℤ) * q) ^ (j + 1) := by
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
  have hpN : (p : ℤ) ≤ (p : ℤ) * q := by nlinarith
  have hqN : (q : ℤ) ≤ (p : ℤ) * q := by nlinarith
  have hp0 : (0 : ℤ) ≤ p := by linarith
  have hq0 : (0 : ℤ) ≤ q := by linarith
  have hpj : (p : ℤ) ^ j ≤ ((p : ℤ) * q) ^ j := pow_le_pow_left₀ hp0 hpN j
  have hqj : (q : ℤ) ^ j ≤ ((p : ℤ) * q) ^ j := pow_le_pow_left₀ hq0 hqN j
  have hNj : (0 : ℤ) < ((p : ℤ) * q) ^ j := by positivity
  rw [gcdMoment_semiprime_four_terms hp hq hpq]
  have e1 : (p : ℤ) ^ (j + 1) * ((q : ℤ) - 1) ≤ ((p : ℤ) * q) ^ (j + 1) := by
    have : (p : ℤ) ^ (j + 1) * ((q : ℤ) - 1) ≤ (p : ℤ) ^ j * ((p : ℤ) * q) := by
      rw [pow_succ]; nlinarith [pow_nonneg hp0 j]
    calc (p : ℤ) ^ (j + 1) * ((q : ℤ) - 1) ≤ (p : ℤ) ^ j * ((p : ℤ) * q) := this
      _ ≤ ((p : ℤ) * q) ^ j * ((p : ℤ) * q) := by nlinarith
      _ = ((p : ℤ) * q) ^ (j + 1) := by rw [pow_succ]
  have e2 : (q : ℤ) ^ (j + 1) * ((p : ℤ) - 1) ≤ ((p : ℤ) * q) ^ (j + 1) := by
    have : (q : ℤ) ^ (j + 1) * ((p : ℤ) - 1) ≤ (q : ℤ) ^ j * ((p : ℤ) * q) := by
      rw [pow_succ]; nlinarith [pow_nonneg hq0 j]
    calc (q : ℤ) ^ (j + 1) * ((p : ℤ) - 1) ≤ (q : ℤ) ^ j * ((p : ℤ) * q) := this
      _ ≤ ((p : ℤ) * q) ^ j * ((p : ℤ) * q) := by nlinarith
      _ = ((p : ℤ) * q) ^ (j + 1) := by rw [pow_succ]
  have e3 : ((p : ℤ) - 1) * ((q : ℤ) - 1) ≤ ((p : ℤ) * q) ^ (j + 1) := by
    have h1 : ((p : ℤ) - 1) * ((q : ℤ) - 1) ≤ (p : ℤ) * q := by nlinarith
    have h2 : ((p : ℤ) * q) ≤ ((p : ℤ) * q) ^ (j + 1) := by
      rw [pow_succ]; nlinarith
    linarith
  linarith

/-- The natural-number form of the upper bound. -/
theorem gcdMoment_le_nat (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    gcdMoment (j + 1) (p * q) ≤ 4 * (p * q) ^ (j + 1) := by
  have h := gcdMoment_le hp hq hpq j
  have : ((gcdMoment (j + 1) (p * q) : ℕ) : ℤ) ≤ ((4 * (p * q) ^ (j + 1) : ℕ) : ℤ) := by
    push_cast; push_cast at h; linarith
  exact_mod_cast this

/-- The variance of `gcd(N, U)^k` for `U` uniform on the residues mod `N`. -/
-- [dropped: platform already declares gcdVariance]
theorem gcdVariance_lower_bound (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    ((p * q : ℕ) : ℚ) ^ (2 * j + 1) - 16 * ((p * q : ℕ) : ℚ) ^ (2 * j)
      ≤ gcdVariance (j + 1) (p * q) := by
  have hNpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hN : (0 : ℚ) < ((p * q : ℕ) : ℚ) := by exact_mod_cast hNpos
  have h1 : ((p * q : ℕ) : ℚ) ^ (2 * j + 2) ≤ (gcdMoment (2 * (j + 1)) (p * q) : ℚ) := by
    have h := gcdMoment_ge (2 * (j + 1)) (p * q) hNpos
    have h' : (((p * q) ^ (2 * (j + 1)) : ℕ) : ℚ) ≤ (gcdMoment (2 * (j + 1)) (p * q) : ℚ) := by
      exact_mod_cast h
    calc ((p * q : ℕ) : ℚ) ^ (2 * j + 2) = (((p * q) ^ (2 * (j + 1)) : ℕ) : ℚ) := by
          push_cast; ring_nf
      _ ≤ _ := h'
  have h2 : (gcdMoment (j + 1) (p * q) : ℚ) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (j + 1) := by
    have h := gcdMoment_le_nat hp hq hpq j
    have h' : ((gcdMoment (j + 1) (p * q) : ℕ) : ℚ) ≤ ((4 * (p * q) ^ (j + 1) : ℕ) : ℚ) := by
      exact_mod_cast h
    calc (gcdMoment (j + 1) (p * q) : ℚ) ≤ ((4 * (p * q) ^ (j + 1) : ℕ) : ℚ) := h'
      _ = 4 * ((p * q : ℕ) : ℚ) ^ (j + 1) := by push_cast; ring
  unfold gcdVariance
  have e1 : ((p * q : ℕ) : ℚ) ^ (2 * j + 1)
      ≤ (gcdMoment (2 * (j + 1)) (p * q) : ℚ) / ((p * q : ℕ) : ℚ) := by
    rw [le_div_iff₀ hN]
    calc ((p * q : ℕ) : ℚ) ^ (2 * j + 1) * ((p * q : ℕ) : ℚ)
        = ((p * q : ℕ) : ℚ) ^ (2 * j + 2) := by ring
      _ ≤ _ := h1
  have e2 : ((gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)) ^ 2
      ≤ 16 * ((p * q : ℕ) : ℚ) ^ (2 * j) := by
    have hdiv : (gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)
        ≤ 4 * ((p * q : ℕ) : ℚ) ^ j := by
      rw [div_le_iff₀ hN]
      calc (gcdMoment (j + 1) (p * q) : ℚ) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (j + 1) := h2
        _ = 4 * ((p * q : ℕ) : ℚ) ^ j * ((p * q : ℕ) : ℚ) := by ring
    have hnn : (0 : ℚ) ≤ (gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ) := by positivity
    calc ((gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)) ^ 2
        ≤ (4 * ((p * q : ℕ) : ℚ) ^ j) ^ 2 := by nlinarith
      _ = 16 * ((p * q : ℕ) : ℚ) ^ (2 * j) := by rw [mul_pow, ← pow_mul]; ring_nf
  linarith

/-- For `k = 1` the variance is at most `4N`: the first moment is the cheap end of the
hierarchy, an `Θ(N)`-sample estimator rather than `Θ(N^{2k−1})`. -/
theorem gcdVariance_one_le (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    gcdVariance 1 (p * q) ≤ 4 * ((p * q : ℕ) : ℚ) := by
  have hNpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hN : (0 : ℚ) < ((p * q : ℕ) : ℚ) := by exact_mod_cast hNpos
  have h2 : (gcdMoment 2 (p * q) : ℚ) ≤ 4 * ((p * q : ℕ) : ℚ) ^ 2 := by
    have h := gcdMoment_le_nat hp hq hpq 1
    have h' : ((gcdMoment 2 (p * q) : ℕ) : ℚ) ≤ ((4 * (p * q) ^ 2 : ℕ) : ℚ) := by
      exact_mod_cast h
    calc (gcdMoment 2 (p * q) : ℚ) ≤ ((4 * (p * q) ^ 2 : ℕ) : ℚ) := h'
      _ = 4 * ((p * q : ℕ) : ℚ) ^ 2 := by push_cast; ring
  unfold gcdVariance
  have hsq : (0 : ℚ) ≤ ((gcdMoment 1 (p * q) : ℚ) / ((p * q : ℕ) : ℚ)) ^ 2 := sq_nonneg _
  have hfirst : (gcdMoment (2 * 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)
      ≤ 4 * ((p * q : ℕ) : ℚ) := by
    rw [div_le_iff₀ hN]
    calc (gcdMoment (2 * 1) (p * q) : ℚ) = (gcdMoment 2 (p * q) : ℚ) := by norm_num
      _ ≤ 4 * ((p * q : ℕ) : ℚ) ^ 2 := h2
      _ = 4 * ((p * q : ℕ) : ℚ) * ((p * q : ℕ) : ℚ) := by ring
  linarith

/-- **The cost separation.**  For `N ≥ 32` the second-moment estimator has variance at least
`N²/8` times the first-moment variance: higher moments are exponentially worse, so the
`O(N)` gcd scan at `k = 1` is the optimal member of the family. -/
theorem gcdVariance_separation (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hbig : (32 : ℚ) ≤ ((p * q : ℕ) : ℚ)) :
    ((p * q : ℕ) : ℚ) ^ 2 / 8 * gcdVariance 1 (p * q) ≤ gcdVariance 2 (p * q) := by
  have hlow := gcdVariance_lower_bound hp hq hpq 1
  have hup := gcdVariance_one_le hp hq hpq
  norm_num at hlow
  have hpos : (0 : ℚ) ≤ ((p * q : ℕ) : ℚ) ^ 2 / 8 := by positivity
  have h1 : ((p * q : ℕ) : ℚ) ^ 2 / 8 * gcdVariance 1 (p * q)
      ≤ ((p * q : ℕ) : ℚ) ^ 2 / 8 * (4 * ((p * q : ℕ) : ℚ)) :=
    mul_le_mul_of_nonneg_left hup hpos
  push_cast at hlow hup hbig hpos h1 ⊢
  nlinarith [hlow, h1, hbig]

/-! ### Witness density -/

/-- **The matching upper bound for the variance.**  Together with `gcdVariance_lower_bound`
this pins the variance of `gcd(N,U)^{j+1}` to the window `[N^{2j+1} − 16N^{2j}, 4N^{2j+1}]`,
so it is `Θ(N^{2k−1})` and the sampling cost hierarchy is tight in order. -/
theorem gcdVariance_upper_bound (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    gcdVariance (j + 1) (p * q) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 1) := by
  have hNpos : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  have hN : (0 : ℚ) < ((p * q : ℕ) : ℚ) := by exact_mod_cast hNpos
  have h2 : (gcdMoment (2 * (j + 1)) (p * q) : ℚ) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 2) := by
    have h := gcdMoment_le_nat hp hq hpq (2 * j + 1)
    have h' : ((gcdMoment (2 * j + 2) (p * q) : ℕ) : ℚ)
        ≤ ((4 * (p * q) ^ (2 * j + 2) : ℕ) : ℚ) := by exact_mod_cast h
    have hidx : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [hidx]
    calc (gcdMoment (2 * j + 2) (p * q) : ℚ) ≤ ((4 * (p * q) ^ (2 * j + 2) : ℕ) : ℚ) := h'
      _ = 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 2) := by push_cast; ring
  have hsq : (0 : ℚ) ≤ ((gcdMoment (j + 1) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)) ^ 2 := sq_nonneg _
  have hdiv : (gcdMoment (2 * (j + 1)) (p * q) : ℚ) / ((p * q : ℕ) : ℚ)
      ≤ 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 1) := by
    rw [div_le_iff₀ hN]
    calc (gcdMoment (2 * (j + 1)) (p * q) : ℚ)
        ≤ 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 2) := h2
      _ = 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 1) * ((p * q : ℕ) : ℚ) := by ring
  unfold gcdVariance
  linarith

/-- The variance is `Θ(N^{2k−1})`: both bounds at once. -/
theorem gcdVariance_theta (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (j : ℕ) :
    ((p * q : ℕ) : ℚ) ^ (2 * j + 1) - 16 * ((p * q : ℕ) : ℚ) ^ (2 * j)
        ≤ gcdVariance (j + 1) (p * q) ∧
      gcdVariance (j + 1) (p * q) ≤ 4 * ((p * q : ℕ) : ℚ) ^ (2 * j + 1) :=
  ⟨gcdVariance_lower_bound hp hq hpq j, gcdVariance_upper_bound hp hq hpq j⟩

/-- **The `Θ(p+q)` query threshold.**  Exactly `p + q − 1` of the `N` probes `x < N` have a
nontrivial gcd with `N`; a uniform probe therefore succeeds with probability `(p+q−1)/N`. -/
theorem card_nontrivial_gcd (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    #{x ∈ Finset.range (p * q) | (p * q).gcd x ≠ 1} = p + q - 1 := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := Finset.range (p * q)) (p := fun x => (p * q).gcd x = 1)
  have hphi : φ (p * q) = #{x ∈ Finset.range (p * q) | (p * q).gcd x = 1} := rfl
  have htot : φ (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hpq), Nat.totient_prime hp,
      Nat.totient_prime hq]
  rw [Finset.card_range, ← hphi, htot] at hcard
  have h2p := hp.two_le
  have h2q := hq.two_le
  have hexp : (p - 1) * (q - 1) + p + q - 1 = p * q := by
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 2 := ⟨q - 2, by omega⟩
    have e1 : (a + 2 - 1) * (b + 2 - 1) = a * b + a + b + 1 := by
      rw [show a + 2 - 1 = a + 1 from rfl, show b + 2 - 1 = b + 1 from rfl]; ring
    have e2 : (a + 2) * (b + 2) = a * b + 2 * a + 2 * b + 4 := by ring
    omega
  have hne : #{x ∈ Finset.range (p * q) | ¬((p * q).gcd x = 1)}
      = #{x ∈ Finset.range (p * q) | (p * q).gcd x ≠ 1} := rfl
  rw [hne] at hcard
  omega

end GCDMoment
-- ==== upstream: Packages/Catalog/Novelty/GCDMomentPairInversion.lean ====
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

namespace GCDMoment

-- [dropped: platform already declares pairMoment]
theorem pairMoment_eq_gcdMoment {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (k : ℕ) :
    pairMoment k (p : ℤ) (q : ℤ) = (gcdMoment k (p * q) : ℤ) := by
  rw [gcdMoment_semiprime_four_terms hp hq hpq, pairMoment]; ring

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

/-- The ambiguity at `k = 2` is real: `28 = 2·14 = 4·7`, and both factorisations predict the
same second moment. -/
theorem pairMoment_two_collision_28 :
    (2 : ℤ) * 14 = 4 * 7 ∧ pairMoment 2 2 14 = pairMoment 2 4 7 ∧ (2 : ℤ) ≠ 4 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [pairMoment_two_eq, pairMoment_two_eq]; norm_num

/-- A second collision at `k = 2`: `36 = 2·18 = 3·12`. -/
theorem pairMoment_two_collision_36 :
    (2 : ℤ) * 18 = 3 * 12 ∧ pairMoment 2 2 18 = pairMoment 2 3 12 ∧ (2 : ℤ) ≠ 3 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  rw [pairMoment_two_eq, pairMoment_two_eq]; norm_num

/-- **Complete classification of the `k = 2` ambiguity.**  `N = 28 = 2·14 = 4·7` and
`N = 36 = 2·18 = 3·12` are the *only* second-moment collisions, over all moduli: the collision
equation `a + b + c + d = N − 1` forces `N ≤ 36`, and a finite check finishes. -/
theorem two_collision_classification {a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b)
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

/-- The cubic bracket controlling the third moment is strictly positive on the admissible
range `2 ≤ a < c ≤ d`.  (Positivity fails at `a = 1`, i.e. for the trivial factorisation.) -/
theorem bracket_pos {a c d : ℤ} (ha : 2 ≤ a) (hac : a < c) (hcd : c ≤ d) :
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

/-- The key algebraic identity: modulo the relation `ab = cd`, the difference of third moments
factors through the bracket, with the explicit cofactor `(c−a)(d−a)/a³`. -/
theorem pairMoment_three_identity {a b c d : ℤ} (h : a * b = c * d) :
    a ^ 3 * (pairMoment 3 a b - pairMoment 3 c d) =
      (c - a) * (d - a) * (a * c * d * (a + c) * (a + d)
        - (a ^ 2 + a * c + c ^ 2) * (a ^ 2 + a * d + d ^ 2) - a ^ 2) := by
  have h3 : (a * b) ^ 3 = (c * d) ^ 3 := by rw [h]
  simp only [pairMoment]
  linear_combination (a ^ 5 + a ^ 3 - a ^ 2) * h + (a ^ 3 + a - 1) * h3

/-- **Strict monotonicity in the spread.**  Among the factorisations of a fixed modulus, the
third moment strictly increases as the factorisation gets more lopsided. -/
theorem pairMoment_three_spread_strict {a b c d : ℤ} (ha : 2 ≤ a) (hac : a < c) (hcd : c ≤ d)
    (h : a * b = c * d) : pairMoment 3 c d < pairMoment 3 a b := by
  have hid := pairMoment_three_identity h
  have hbr := bracket_pos ha hac hcd
  have hca : 0 < c - a := by linarith
  have hda : 0 < d - a := by linarith
  have hpos : 0 < (c - a) * (d - a) * (a * c * d * (a + c) * (a + d)
      - (a ^ 2 + a * c + c ^ 2) * (a ^ 2 + a * d + d ^ 2) - a ^ 2) :=
    mul_pos (mul_pos hca hda) hbr
  have ha3 : 0 < a ^ 3 := by positivity
  nlinarith [hid, hpos, ha3]

/-- **Identifiability at `k = 3`.**  Two nontrivial factorisations of the same modulus with the
same third moment are equal.  In particular no size cut is needed at `k = 3`, in contrast with
`k = 2`. -/
theorem pairMoment_three_injective {a b c d : ℤ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 2 ≤ c)
    (hcd : c ≤ d) (h : a * b = c * d) (hm : pairMoment 3 a b = pairMoment 3 c d) :
    a = c ∧ b = d := by
  have hac : a = c := by
    rcases lt_trichotomy a c with hlt | heq | hgt
    · exact absurd hm (by have := pairMoment_three_spread_strict ha hlt hcd h; linarith)
    · exact heq
    · exact absurd hm.symm
        (by have := pairMoment_three_spread_strict hc hgt hab h.symm; linarith)
  refine ⟨hac, ?_⟩
  have ha0 : a ≠ 0 := by linarith
  have : a * b = a * d := by rw [h, hac]
  exact mul_left_cancel₀ ha0 this

/-- **The arithmetic payoff.**  For a semiprime `N = p q` the observed third gcd moment
identifies the factorisation among all nontrivial factorisations of `N`. -/
theorem gcdMoment_three_identifies_factors {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hle : p ≤ q) (ha : 2 ≤ a) (hab : a ≤ b) (hprod : a * b = p * q)
    (hm : pairMoment 3 (a : ℤ) (b : ℤ) = (gcdMoment 3 (p * q) : ℤ)) :
    a = p ∧ b = q := by
  have hprodZ : (a : ℤ) * b = (p : ℤ) * q := by exact_mod_cast hprod
  have hmm : pairMoment 3 (a : ℤ) b = pairMoment 3 (p : ℤ) q := by
    rw [hm, pairMoment_eq_gcdMoment hp hq hpq]
  have haZ : (2 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have habZ : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
  have hpZ : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have hleZ : (p : ℤ) ≤ (q : ℤ) := by exact_mod_cast hle
  obtain ⟨h1, h2⟩ := pairMoment_three_injective haZ habZ hpZ hleZ hprodZ hmm
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **The second moment does factor a genuine semiprime.**  The two collisions of
`two_collision_classification` occur at `N = 28` and `N = 36`, and neither is a product of two
*distinct primes* — in both collisions one of the two factors involved is composite.  Hence for
a distinct-prime semiprime the second-moment oracle is already unambiguous, even though the
`k = 2` moment polynomial has a second root. -/
theorem factorization_from_second_moment {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hprod : a * b = p * q)
    (hmatch : pairMoment 2 (a : ℤ) (b : ℤ) = (gcdMoment 2 (p * q) : ℤ)) : a = p ∧ b = q := by
  have htrue : pairMoment 2 (p : ℤ) (q : ℤ) = (gcdMoment 2 (p * q) : ℤ) :=
    pairMoment_eq_gcdMoment hp hq (by omega) 2
  have hcoll : pairMoment 2 (a : ℤ) (b : ℤ) = pairMoment 2 (p : ℤ) (q : ℤ) := by
    rw [hmatch, htrue]
  have hac : a = p := by
    rcases lt_trichotomy a p with hlt | heq | hgt
    · rcases two_collision_classification ha hab (le_of_lt hpq) hlt hprod hcoll with
        ⟨-, -, h3, -⟩ | ⟨-, -, -, h4⟩
      · exact absurd (h3 ▸ hp) (by norm_num)
      · exact absurd (h4 ▸ hq) (by norm_num)
    · exact heq
    · rcases two_collision_classification hp.two_le (le_of_lt hpq) hab hgt hprod.symm
        hcoll.symm with ⟨-, h2, -, -⟩ | ⟨-, h2, -, -⟩
      · exact absurd (h2 ▸ hq) (by norm_num)
      · exact absurd (h2 ▸ hq) (by norm_num)
  refine ⟨hac, ?_⟩
  have ha0 : 0 < a := by omega
  have : a * b = a * q := by rw [hprod, hac]
  exact Nat.eq_of_mul_eq_mul_left ha0 this

/-- **The first moment factors a semiprime too**, in the same `pairMoment` language: matching
the first moment forces the candidate trace to equal the true one. -/
theorem factorization_from_first_moment {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
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

end GCDMoment
-- ==== upstream: Packages/Catalog/Novelty/GCDMomentMultiplicative.lean ====
/-!
# The gcd moments are a multiplicative family: beyond semiprimes

`Novelty.GCDMomentTraceWitness` computes `M_k(N) = ∑_{x < N} gcd(N,x)^k` for a *semiprime*
`N = pq` and reads off the trace-witness structure.  This file removes the semiprime
restriction: `M_k` is the Dirichlet convolution `(n ↦ n^k) * φ`, hence multiplicative, so its
value at an arbitrary modulus is a product over the prime-power part of the factorisation.

The consequence for the trace-witness picture is sharp.  For a *squarefree* modulus

`M_k(n) = ∏_{p ∣ n} (p^k + p − 1)`,

so the moment is an Euler product over the prime factors: it is not just a symmetric function
of the factors, it is a **completely split** one, with one local factor per prime.  Specialising
to `n = pq` reproduces the semiprime four-term formula, and shows that the four terms of the
closed form are nothing but the expansion of a two-factor Euler product.

## Main results

* `gcdMomentAF` — the gcd moment as an arithmetic function, `pow k * phiAF`.
* `gcdMomentAF_isMultiplicative` — multiplicativity.
* `gcdMomentAF_apply_eq` — the arithmetic function agrees with `gcdMoment` on `n > 0`.
* `gcdMoment_mul_of_coprime` — `M_k(mn) = M_k(m) M_k(n)` for coprime `m, n > 0`.
* `gcdMoment_prime` — the local factor `M_k(p) = p^k + p − 1`.
* `gcdMoment_prime_pow`, `gcdMoment_prime_pow_closed` — the local factor at a prime power,
  `∑_{i ≤ e} p^{ik} φ(p^{e−i}) = p^{ek} + (p−1)∑_{i<e} p^{ik} p^{e−1−i}`.
* `gcdMoment_squarefree` — **the Euler product** `M_k(n) = ∏_{p ∣ n} (p^k + p − 1)`.
* `gcdMoment_ge_local`, `gcdMoment_gt_local_of_not_prime`, `gcdMoment_eq_local_iff_prime` —
  **the moment detects primality**: `M_k(n) ≥ n^k + n − 1` always, with equality iff `n` is
  prime.
* `gcdMoment_semiprime_euler` — the semiprime case as a two-factor product, and
  `gcdMoment_semiprime_euler_eq_four_terms` — its agreement with the closed form of the
  companion file.
* `gcdMoment_factorization` — the general modulus: a product over the prime factorisation.
* `pairMoment_eq_euler` — the predicted moment of a *candidate* factorisation is the same
  two-factor Euler product, which is what makes the inversion analysis of the companion files
  a statement about local factors.
* `euler_local_factor_refine`, `pairMoment_gt_trivial` — the local factor `t ↦ t^k + t − 1` is
  strictly submultiplicative on `t ≥ 2`: refining a factorisation strictly raises the moment.
* `eulerProd_ge_eulerLocal`, `eulerProd_gt_eulerLocal` — the same for an arbitrary number of
  factors: any splitting into `r ≥ 2` parts strictly raises the predicted moment.
-/

namespace GCDMoment

open Finset ArithmeticFunction

-- [dropped: platform already declares phiAF]
@[simp] lemma phiAF_apply (n : ℕ) : phiAF n = n.totient := rfl

lemma phiAF_isMultiplicative : phiAF.IsMultiplicative := by
  constructor
  · simp
  · intro m n h
    simp [Nat.totient_mul h]

/-- The `k`-th gcd moment as an arithmetic function: the Dirichlet convolution of `n ↦ n^k`
with Euler's totient. -/
-- [dropped: platform already declares gcdMomentAF]
theorem gcdMomentAF_isMultiplicative (k : ℕ) : (gcdMomentAF k).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_pow.mul phiAF_isMultiplicative

lemma gcdMomentAF_apply (k n : ℕ) :
    gcdMomentAF k n = ∑ d ∈ n.divisors, d ^ k * (n / d).totient := by
  rw [gcdMomentAF, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => ArithmeticFunction.pow k x * phiAF y)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rcases Nat.mem_divisors.1 hd with ⟨hdvd, hn⟩
    rintro rfl
    exact hn (Nat.eq_zero_of_zero_dvd hdvd)
  simp [ArithmeticFunction.pow_apply, hd0]

/-- The arithmetic function computes the gcd moment. -/
theorem gcdMomentAF_apply_eq (k n : ℕ) (hn : 0 < n) : gcdMomentAF k n = gcdMoment k n := by
  rw [gcdMomentAF_apply, gcdMoment_eq_sum_divisors k n hn]

/-- **The gcd moment is multiplicative**, in elementary terms. -/
theorem gcdMoment_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n)
    (k : ℕ) : gcdMoment k (m * n) = gcdMoment k m * gcdMoment k n := by
  have := (gcdMomentAF_isMultiplicative k).2 h
  rw [gcdMomentAF_apply_eq k _ (Nat.mul_pos hm hn), gcdMomentAF_apply_eq k m hm,
    gcdMomentAF_apply_eq k n hn] at this
  exact this

/-- **The local factor at a prime**: `M_k(p) = p^k + p − 1`. -/
theorem gcdMoment_prime {p : ℕ} (hp : p.Prime) (k : ℕ) : gcdMoment k p = p ^ k + p - 1 := by
  rw [← gcdMomentAF_apply_eq k p hp.pos, gcdMomentAF_apply, hp.divisors]
  rw [Finset.sum_pair hp.one_lt.ne]
  rw [Nat.div_self hp.pos, Nat.div_one, Nat.totient_prime hp]
  have : 1 ≤ p := hp.pos
  simp only [one_pow, one_mul, Nat.totient_one, mul_one]
  omega

/-- **The local factor at a prime power.** -/
theorem gcdMoment_prime_pow {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    gcdMoment k (p ^ e) = ∑ i ∈ Finset.range (e + 1), p ^ (i * k) * (p ^ (e - i)).totient := by
  rw [← gcdMomentAF_apply_eq k _ (pow_pos hp.pos e), gcdMomentAF_apply,
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hile : i ≤ e := by simpa [Nat.lt_succ_iff] using hi
  rw [Nat.pow_div hile hp.pos, ← pow_mul]

/-- **Closed form of the local factor at a prime power.**  `M_k(p^e) = p^{ek} + (p−1)·∑_{i<e}
p^{ik}·p^{e−1−i}`, which for `e = 1` is the prime factor `p^k + p − 1`. -/
theorem gcdMoment_prime_pow_closed {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    gcdMoment k (p ^ e)
      = p ^ (e * k) + (p - 1) * ∑ i ∈ Finset.range e, p ^ (i * k) * p ^ (e - 1 - i) := by
  rw [gcdMoment_prime_pow hp e k, Finset.sum_range_succ, Nat.sub_self, pow_zero,
    Nat.totient_one, mul_one, Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hie : i < e := Finset.mem_range.1 hi
  have hpos : 0 < e - i := by omega
  rw [Nat.totient_prime_pow hp hpos]
  have hidx : e - i - 1 = e - 1 - i := by omega
  rw [hidx]
  ring

/-- **The Euler product for a squarefree modulus.**  Every gcd moment splits completely into
one local factor per prime divisor. -/
theorem gcdMoment_squarefree {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    gcdMoment k n = ∏ p ∈ n.primeFactors, (p ^ k + p - 1) := by
  have hn0 : 0 < n := hn.ne_zero.bot_lt
  rw [← gcdMomentAF_apply_eq k n hn0]
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hn]
  rw [(gcdMomentAF_isMultiplicative k).map_prod _ n.primeFactors
      (fun p hp q hq hpq => (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).2 hpq)]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  rw [gcdMomentAF_apply_eq k p hpp.pos, gcdMoment_prime hpp]

/-! ### The moment detects primality exactly

Gauss's identity `∑_{d ∣ n} φ(d) = n` gives a universal lower bound `M_k(n) ≥ n^k + n − 1`,
attained precisely at the primes.  So the local Euler factor is not merely the value of the
moment at a prime: it is the *minimum* of the moment over all moduli of a given size, and the
excess `M_k(n) − (n^k + n − 1)` is a strictly positive measure of how composite `n` is. -/

/-- **The universal lower bound.**  `M_k(n) ≥ n^k + n − 1` for every `n > 0`, by Gauss's
totient identity. -/
theorem gcdMoment_ge_local {n : ℕ} (hn : 0 < n) (k : ℕ) : n ^ k + n - 1 ≤ gcdMoment k n := by
  classical
  rw [gcdMoment_eq_sum_divisors k n hn]
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hg : ∑ d ∈ n.divisors, Nat.totient (n / d) = n := by
    rw [Nat.sum_div_divisors]; exact Nat.sum_totient n
  have hgsplit := Finset.add_sum_erase n.divisors (fun d => Nat.totient (n / d)) hmem
  rw [hg] at hgsplit
  simp only [Nat.div_self hn, Nat.totient_one] at hgsplit
  have hle : ∑ d ∈ n.divisors.erase n, Nat.totient (n / d)
      ≤ ∑ d ∈ n.divisors.erase n, d ^ k * Nat.totient (n / d) := by
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd)
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hsplit := Finset.add_sum_erase n.divisors (fun d => d ^ k * Nat.totient (n / d)) hmem
  simp only [Nat.div_self hn, Nat.totient_one, mul_one] at hsplit
  omega

/-- **Strictness at composite moduli.**  Any nontrivial divisor contributes a strict excess. -/
theorem gcdMoment_gt_local_of_not_prime {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) {k : ℕ}
    (hk : 1 ≤ k) : n ^ k + n - 1 < gcdMoment k n := by
  classical
  have hn0 : 0 < n := by omega
  rw [gcdMoment_eq_sum_divisors k n hn0]
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn0.ne'
  have hg : ∑ d ∈ n.divisors, Nat.totient (n / d) = n := by
    rw [Nat.sum_div_divisors]; exact Nat.sum_totient n
  have hgsplit := Finset.add_sum_erase n.divisors (fun d => Nat.totient (n / d)) hmem
  rw [hg] at hgsplit
  simp only [Nat.div_self hn0, Nat.totient_one] at hgsplit
  obtain ⟨m, hmdvd, hm1, hmn⟩ : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
    by_contra hc
    push_neg at hc
    exact hnp (Nat.prime_def.2 ⟨hn, fun m hm => by
      rcases eq_or_ne m 1 with rfl | h1
      · exact Or.inl rfl
      · exact Or.inr (hc m hm h1)⟩)
  have hmem' : m ∈ n.divisors.erase n :=
    Finset.mem_erase.2 ⟨hmn, Nat.mem_divisors.2 ⟨hmdvd, hn0.ne'⟩⟩
  have hlt : ∑ d ∈ n.divisors.erase n, Nat.totient (n / d)
      < ∑ d ∈ n.divisors.erase n, d ^ k * Nat.totient (n / d) := by
    refine Finset.sum_lt_sum (fun d hd => ?_) ⟨m, hmem', ?_⟩
    · have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd)
      exact Nat.le_mul_of_pos_left _ (by positivity)
    · have hm0 : 0 < m := Nat.pos_of_mem_divisors (Nat.mem_divisors.2 ⟨hmdvd, hn0.ne'⟩)
      have hm2 : 2 ≤ m := by omega
      have hmk : 2 ≤ m ^ k := le_trans hm2 (Nat.le_self_pow (by omega) m)
      have htot : 0 < Nat.totient (n / m) :=
        Nat.totient_pos.2 (Nat.div_pos (Nat.le_of_dvd hn0 hmdvd) hm0)
      calc Nat.totient (n / m) < 2 * Nat.totient (n / m) := by omega
        _ ≤ m ^ k * Nat.totient (n / m) := Nat.mul_le_mul_right _ hmk
  have hsplit := Finset.add_sum_erase n.divisors (fun d => d ^ k * Nat.totient (n / d)) hmem
  simp only [Nat.div_self hn0, Nat.totient_one, mul_one] at hsplit
  omega

/-- **Primality criterion.**  For `n ≥ 2` and `k ≥ 1`, the `k`-th gcd moment attains its
universal lower bound exactly at the primes. -/
theorem gcdMoment_eq_local_iff_prime {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    gcdMoment k n = n ^ k + n - 1 ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnp
    exact absurd h (by have := gcdMoment_gt_local_of_not_prime hn hnp hk; omega)
  · intro hp
    exact gcdMoment_prime hp k

/-- The semiprime case is a two-factor Euler product. -/
theorem gcdMoment_semiprime_euler {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (k : ℕ) : gcdMoment k (p * q) = (p ^ k + p - 1) * (q ^ k + q - 1) := by
  rw [gcdMoment_mul_of_coprime hp.pos hq.pos ((Nat.coprime_primes hp hq).2 hpq) k,
    gcdMoment_prime hp, gcdMoment_prime hq]

/-- Consistency: the Euler product expands to the four-term closed form of the companion file,
so the "four terms" are exactly the four terms of a two-factor Euler product. -/
theorem gcdMoment_semiprime_euler_eq_four_terms {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (k : ℕ) :
    (gcdMoment k (p * q) : ℤ) = ((p : ℤ) ^ k + (p : ℤ) - 1) * ((q : ℤ) ^ k + (q : ℤ) - 1) := by
  rw [gcdMoment_semiprime_four_terms hp hq hpq k]
  ring

/-! ### The predicted moment is itself an Euler product

The inversion analysis of `Novelty.GCDMomentPairInversion` is built on `pairMoment`, the moment
a candidate factorisation `N = ab` predicts.  The multiplicative picture explains its shape: it
is exactly the two-factor Euler product with the *candidate* factors in place of the primes.
Monotonicity in the spread — the engine of the identifiability theorems — is therefore the
statement that the local factor `t ↦ t^k + t − 1` is log-convex enough to make the product
increase as the factors move apart. -/

/-- **`pairMoment` is the two-factor Euler product.** -/
theorem pairMoment_eq_euler (k : ℕ) (a b : ℤ) :
    pairMoment k a b = (a ^ k + a - 1) * (b ^ k + b - 1) := by
  simp only [pairMoment]; ring

/-- The prediction of the true factorisation is the true moment, seen through the Euler
product: this re-derives `gcdMoment_semiprime_euler` from multiplicativity alone. -/
theorem pairMoment_prime_pair_eq_gcdMoment {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (k : ℕ) :
    pairMoment k (p : ℤ) (q : ℤ) = (((p ^ k + p - 1) * (q ^ k + q - 1) : ℕ) : ℤ) := by
  have h1 : 1 ≤ p ^ k + p := le_trans hp.pos (Nat.le_add_left p _)
  have h2 : 1 ≤ q ^ k + q := le_trans hq.pos (Nat.le_add_left q _)
  rw [pairMoment_eq_euler]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
  ring

/-- **Refinement strictly increases the Euler product.**  Splitting a factor `uv` into `u` and
`v` (both `≥ 2`) strictly increases the predicted moment, for every `k ≥ 1`.  Equivalently, the
local factor `L_k(t) = t^k + t − 1` is strictly submultiplicative on `t ≥ 2`. -/
theorem euler_local_factor_refine {u v : ℤ} (hu : 2 ≤ u) (hv : 2 ≤ v) {k : ℕ} (hk : 1 ≤ k) :
    (u * v) ^ k + u * v - 1 < (u ^ k + u - 1) * (v ^ k + v - 1) := by
  have hk0 : k ≠ 0 := by omega
  have hu1 : (1 : ℤ) ≤ u := by linarith
  have hv1 : (1 : ℤ) ≤ v := by linarith
  have hupow : u ≤ u ^ k := le_self_pow₀ hu1 hk0
  have hvpow : v ≤ v ^ k := le_self_pow₀ hv1 hk0
  have hmul : (u * v) ^ k = u ^ k * v ^ k := mul_pow u v k
  have h1 : (0 : ℤ) < (u - 1) * (v - 1) := mul_pos (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.2 hupow) (sub_nonneg.2 hv1),
    mul_nonneg (sub_nonneg.2 hvpow) (sub_nonneg.2 hu1)]

/-- The same statement in `pairMoment` form: any genuine splitting of the modulus predicts a
larger moment than the trivial factorisation. -/
theorem pairMoment_gt_trivial {u v : ℤ} (hu : 2 ≤ u) (hv : 2 ≤ v) {k : ℕ} (hk : 1 ≤ k) :
    (u * v) ^ k + u * v - 1 < pairMoment k u v := by
  rw [pairMoment_eq_euler]
  exact euler_local_factor_refine hu hv hk

/-! ### The `r`-factor refinement law -/

/-- The local Euler factor `L_k(a) = a^k + a − 1`. -/
-- [dropped: platform already declares eulerLocal]
-- [dropped: platform already declares eulerProd]
lemma eulerLocal_refine {u v : ℤ} (hu : 2 ≤ u) (hv : 2 ≤ v) {k : ℕ} (hk : 1 ≤ k) :
    eulerLocal k (u * v) < eulerLocal k u * eulerLocal k v := by
  simpa [eulerLocal] using euler_local_factor_refine hu hv hk

lemma three_le_eulerLocal {a : ℤ} (ha : 2 ≤ a) {k : ℕ} (hk : 1 ≤ k) : 3 ≤ eulerLocal k a := by
  have : a ≤ a ^ k := le_self_pow₀ (by linarith) (by omega)
  simp only [eulerLocal]; linarith

lemma two_le_list_prod : ∀ (l : List ℤ), l ≠ [] → (∀ a ∈ l, 2 ≤ a) → 2 ≤ l.prod
  | [], h, _ => absurd rfl h
  | [a], _, h => by simpa using h a (by simp)
  | (a :: b :: t), _, h => by
      have ha : 2 ≤ a := h a (by simp)
      have hrest : 2 ≤ (b :: t).prod :=
        two_le_list_prod (b :: t) (by simp) (fun x hx => h x (by simp [hx]))
      rw [List.prod_cons]
      nlinarith

/-- **Refinement monotonicity for an arbitrary number of factors.**  The Euler product over any
factorisation into parts `≥ 2` is at least the single local factor of the whole product. -/
theorem eulerProd_ge_eulerLocal {k : ℕ} (hk : 1 ≤ k) : ∀ (l : List ℤ), l ≠ [] →
    (∀ a ∈ l, 2 ≤ a) → eulerLocal k l.prod ≤ eulerProd k l
  | [], h, _ => absurd rfl h
  | [_], _, _ => by simp [eulerProd]
  | (a :: b :: t), _, h => by
      have ha : 2 ≤ a := h a (by simp)
      have hrest : 2 ≤ (b :: t).prod :=
        two_le_list_prod _ (by simp) (fun x hx => h x (by simp [hx]))
      have ih : eulerLocal k (b :: t).prod ≤ eulerProd k (b :: t) :=
        eulerProd_ge_eulerLocal hk (b :: t) (by simp) (fun x hx => h x (by simp [hx]))
      have hla : (0 : ℤ) < eulerLocal k a := by
        have := three_le_eulerLocal ha hk; linarith
      have hstep := eulerLocal_refine ha hrest hk
      have hmul := mul_le_mul_of_nonneg_left ih (le_of_lt hla)
      have hsplit : eulerProd k (a :: b :: t) = eulerLocal k a * eulerProd k (b :: t) := by
        simp [eulerProd]
      rw [hsplit, List.prod_cons]
      linarith

/-- **Strict refinement.**  As soon as the factorisation has at least two parts, the Euler
product strictly exceeds the local factor of the modulus: a genuine splitting is always visible
in the moment. -/
theorem eulerProd_gt_eulerLocal {k : ℕ} (hk : 1 ≤ k) (a : ℤ) (l : List ℤ) (hne : l ≠ [])
    (h : ∀ x ∈ a :: l, 2 ≤ x) : eulerLocal k (a :: l).prod < eulerProd k (a :: l) := by
  have ha : 2 ≤ a := h a (by simp)
  have hrest : 2 ≤ l.prod := two_le_list_prod l hne (fun x hx => h x (by simp [hx]))
  have ih : eulerLocal k l.prod ≤ eulerProd k l :=
    eulerProd_ge_eulerLocal hk l hne (fun x hx => h x (by simp [hx]))
  have hla : (0 : ℤ) < eulerLocal k a := by have := three_le_eulerLocal ha hk; linarith
  have hstep := eulerLocal_refine ha hrest hk
  have hmul := mul_le_mul_of_nonneg_left ih (le_of_lt hla)
  have hsplit : eulerProd k (a :: l) = eulerLocal k a * eulerProd k l := by simp [eulerProd]
  rw [hsplit, List.prod_cons]
  linarith

/-- **The general modulus.**  For any `n > 0` the moment is the product of its local factors. -/
theorem gcdMoment_factorization (k : ℕ) {n : ℕ} (hn : 0 < n) :
    gcdMoment k n = n.factorization.prod fun p e => gcdMoment k (p ^ e) := by
  rw [← gcdMomentAF_apply_eq k n hn,
    (gcdMomentAF_isMultiplicative k).multiplicative_factorization _ hn.ne']
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  exact gcdMomentAF_apply_eq k _ (pow_pos hpp.pos _)

/-- Sanity checks of the Euler product against brute-force enumeration:
`M_2(6) = (2²+2−1)(3²+3−1) = 5·11` and `M_3(30) = 9·29·129`. -/
example : gcdMoment 2 6 = (2 ^ 2 + 2 - 1) * (3 ^ 2 + 3 - 1) := by decide
example : gcdMoment 3 30 = (2 ^ 3 + 2 - 1) * (3 ^ 3 + 3 - 1) * (5 ^ 3 + 5 - 1) := by decide
example : gcdMoment 2 12 = gcdMoment 2 4 * gcdMoment 2 3 := by decide

end GCDMoment
-- ==== upstream: Packages/Catalog/Novelty/GCDMomentRefinementOrder.lean ====
/-!
# The refinement order on gcd moments: the prime factorisation is the maximum

This file is the third cycle of the gcd-moment project
(`Novelty.GCDMomentTraceWitness`, `Novelty.GCDMomentPairInversion`,
`Novelty.GCDMomentMultiplicative`).  The previous cycle proved the *bottom* of the refinement
order: the moment of a modulus is at least its own local Euler factor
(`gcdMoment_ge_local`), with equality exactly at the primes, and splitting a factor strictly
raises the *predicted* Euler product (`eulerProd_gt_eulerLocal`).

Here we prove the *top* of that order.  Write

`Π_k(n) = ∏_{p ∈ primeFactorsList n} (p^k + p − 1)`

for the Euler product read off the full prime factorisation counted with multiplicity
(`primeProd`, the finest possible factorisation of `n`).  Then:

## Main results

* `gcdMoment_prime_pow_succ` — the local recursion `M_k(p^{e+1}) = p^k M_k(p^e) + φ(p^{e+1})`,
  which drives every estimate below.
* `gcdMoment_prime_pow_le`, `gcdMoment_prime_pow_lt` — `M_k(p^e) ≤ (p^k+p−1)^e`, strictly as
  soon as `e ≥ 2`: a prime power is *cheaper* than the same number of independent primes.
* `gcdMoment_prime_sq_deficiency`, `gcdMoment_prime_pow_deficiency` — the exact gap at a
  square, `(p^k+p−1)^2 − M_k(p^2) = (p−1)(p^k−1)`, and its closed form at every prime power.
* `gcdMoment_le_primeProd` — **the upper envelope**: `M_k(n) ≤ Π_k(n)` for every `n > 0`
  and every `k ≥ 1`.
* `gcdMoment_eq_primeProd_iff_squarefree` — **equality holds exactly on the squarefree moduli**.
  Together with `gcdMoment_eq_local_iff_prime` (previous cycle) this brackets the moment
  between two Euler products whose equality cases are precisely "`n` prime" and
  "`n` squarefree": `n^k + n − 1 ≤ M_k(n) ≤ Π_k(n)`.
* `factorisationEuler_le_primeProd` — **the prime factorisation maximises the predicted
  moment**: for *any* factorisation `n = a_1 ⋯ a_r` into parts `≥ 2`, the predicted Euler
  product `∏_i (a_i^k + a_i − 1)` is at most `Π_k(n)`; combined with `eulerProd_ge_eulerLocal`
  the refinement order is now pinned at both ends.
* `primeProd_mul`, `primeProd_prime_pow` — `Π_k` is completely multiplicative, which is what
  makes the induction work and is the exact sense in which the *finest* factorisation is a
  "free" object.

## Lab notes (data behind the statements)

Brute-force values (checked by `decide` at the end of the file):

| `n` | `M_2(n)` | `Π_2(n)` | squarefree? |
|-----|----------|----------|-------------|
| 6   | 55       | 55       | yes |
| 12  | 242      | 275      | no  |
| 4   | 22       | 25       | no  |
| 8   | 92       | 125      | no  |
| 9   | 105      | 121      | no  |

so the gap `Π_k(n) − M_k(n)` is a strictly positive measure of non-squarefreeness, and it is
`0` on the squarefree locus.  The semiprime moduli of the factoring-barrier files are
squarefree, so on them the moment *is* the full Euler product — which is exactly why the
inversion analysis of the previous cycles is possible there and nowhere else.
-/

namespace GCDMoment

open Finset

/-! ### The local recursion at a prime power -/

/-- **The local recursion.**  `M_k(p^{e+1}) = p^k · M_k(p^e) + φ(p^{e+1})`. -/
theorem gcdMoment_prime_pow_succ {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    gcdMoment k (p ^ (e + 1)) = p ^ k * gcdMoment k (p ^ e) + (p ^ (e + 1)).totient := by
  rw [gcdMoment_prime_pow hp (e + 1) k, gcdMoment_prime_pow hp e k, Finset.mul_sum,
    Finset.sum_range_succ']
  simp only [Nat.zero_mul, pow_zero, one_mul, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hile : i ≤ e := by simpa [Nat.lt_succ_iff] using hi
  have h1 : e + 1 - (i + 1) = e - i := by omega
  rw [h1, ← mul_assoc, ← pow_add]
  ring_nf

/-- The local factor at a prime, in additive form (no truncated subtraction). -/
lemma gcdMoment_prime_add {p : ℕ} (hp : p.Prime) (k : ℕ) :
    gcdMoment k p = p ^ k + (p - 1) := by
  have h1 : 1 ≤ p := hp.pos
  rw [gcdMoment_prime hp k]
  omega

/-- The prime local factor dominates the prime: `p < p^k + p − 1` for `k ≥ 1`, `p ≥ 2`. -/
lemma lt_gcdMoment_prime {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    p < gcdMoment k p := by
  have h2 : 2 ≤ p := hp.two_le
  have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
  rw [gcdMoment_prime_add hp]
  omega

/-- **A prime power is cheaper than independent primes**: `M_k(p^e) ≤ (p^k + p − 1)^e`. -/
theorem gcdMoment_prime_pow_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) (e : ℕ) :
    gcdMoment k (p ^ e) ≤ gcdMoment k p ^ e := by
  induction e with
  | zero => simp [gcdMoment]
  | succ e ih =>
      have h2 : 2 ≤ p := hp.two_le
      have hple : p ≤ gcdMoment k p := (lt_gcdMoment_prime hp hk).le
      have hpow : p ^ e ≤ gcdMoment k p ^ e := Nat.pow_le_pow_left hple e
      have htot : (p ^ (e + 1)).totient = p ^ e * (p - 1) := by
        rw [Nat.totient_prime_pow hp (Nat.succ_pos e)]
        simp
      have hstep := gcdMoment_prime_pow_succ hp e k
      have hmul : p ^ k * gcdMoment k (p ^ e) ≤ p ^ k * gcdMoment k p ^ e :=
        Nat.mul_le_mul_left _ ih
      have hsub : p ^ e * (p - 1) ≤ gcdMoment k p ^ e * (p - 1) :=
        Nat.mul_le_mul_right _ hpow
      have hexp : gcdMoment k p ^ (e + 1)
          = p ^ k * gcdMoment k p ^ e + gcdMoment k p ^ e * (p - 1) := by
        rw [pow_succ, gcdMoment_prime_add hp]
        ring
      rw [hstep, htot, hexp]
      omega

/-- **Strictly cheaper**: for `e ≥ 2` the prime power is strictly below the `e`-fold local
factor.  This is the source of the squarefree equality criterion below. -/
theorem gcdMoment_prime_pow_lt {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) {e : ℕ}
    (he : 2 ≤ e) : gcdMoment k (p ^ e) < gcdMoment k p ^ e := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
  have hf : 1 ≤ f := by omega
  have h2 : 2 ≤ p := hp.two_le
  have hplt : p < gcdMoment k p := lt_gcdMoment_prime hp hk
  have hpow : p ^ f < gcdMoment k p ^ f := by
    exact Nat.pow_lt_pow_left hplt (by omega)
  have htot : (p ^ (f + 1)).totient = p ^ f * (p - 1) := by
    rw [Nat.totient_prime_pow hp (Nat.succ_pos f)]
    simp
  have hstep := gcdMoment_prime_pow_succ hp f k
  have hmul : p ^ k * gcdMoment k (p ^ f) ≤ p ^ k * gcdMoment k p ^ f :=
    Nat.mul_le_mul_left _ (gcdMoment_prime_pow_le hp hk f)
  have hsub : p ^ f * (p - 1) < gcdMoment k p ^ f * (p - 1) := by
    have : 0 < p - 1 := by omega
    exact Nat.mul_lt_mul_of_lt_of_le hpow (le_refl _) this
  have hexp : gcdMoment k p ^ (f + 1)
      = p ^ k * gcdMoment k p ^ f + gcdMoment k p ^ f * (p - 1) := by
    rw [pow_succ, gcdMoment_prime_add hp]
    ring
  rw [hstep, htot, hexp]
  omega

/-- **The exact deficiency at a square.**  `(p^k + p − 1)^2 − M_k(p^2) = (p − 1)(p^k − 1)`:
the gap between the moment of `p^2` and the moment predicted by the factorisation `p · p` is an
explicit positive quantity, so the moment distinguishes `p^2` from a product of two *distinct*
primes of the same size. -/
theorem gcdMoment_prime_sq_deficiency {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    gcdMoment k (p ^ 2) + (p - 1) * (p ^ k - 1) = gcdMoment k p ^ 2 := by
  have h2 : 2 ≤ p := hp.two_le
  obtain ⟨a, ha⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  have hpk : p ≤ p ^ k := Nat.le_self_pow (by omega) p
  obtain ⟨c, hc⟩ : ∃ c, p ^ k = c + 1 := ⟨p ^ k - 1, by omega⟩
  have hstep := gcdMoment_prime_pow_succ hp 1 k
  have h1 : gcdMoment k (p ^ 1) = p ^ k + (p - 1) := by
    rw [pow_one, gcdMoment_prime_add hp]
  have htot : (p ^ (1 + 1)).totient = p * (p - 1) := by
    rw [Nat.totient_prime_pow hp (by norm_num)]
    simp
  have hsq : (p : ℕ) ^ 2 = p ^ (1 + 1) := by norm_num
  have hL : gcdMoment k p = p ^ k + (p - 1) := gcdMoment_prime_add hp k
  rw [hsq, hstep, h1, htot, hL, hc, ha]
  simp only [Nat.add_sub_cancel]
  ring

/-- **The exact deficiency at every prime power.**  With `L = M_k(p) = p^k + p − 1`,

`L^e − M_k(p^e) = (p − 1) ∑_{i < e} p^{ik} (L^{e−1−i} − p^{e−1−i})`,

an explicit finite sum of geometric differences; at `e = 2` it collapses to
`(p−1)(p^k−1)` and at `e ≤ 1` to `0`.  This is the quantitative form of
`gcdMoment_prime_pow_lt`. -/
theorem gcdMoment_prime_pow_deficiency {p : ℕ} (hp : p.Prime) (k e : ℕ) :
    (gcdMoment k p : ℤ) ^ e - (gcdMoment k (p ^ e) : ℤ)
      = ((p : ℤ) - 1) * ∑ i ∈ Finset.range e, (p : ℤ) ^ (i * k) *
          ((gcdMoment k p : ℤ) ^ (e - 1 - i) - (p : ℤ) ^ (e - 1 - i)) := by
  have h2 : 2 ≤ p := hp.two_le
  have hL : (gcdMoment k p : ℤ) = (p : ℤ) ^ k + ((p : ℤ) - 1) := by
    have := gcdMoment_prime_add hp k
    have h1 : 1 ≤ p := by omega
    rw [this]
    push_cast [Nat.cast_sub h1]
    ring
  induction e with
  | zero => simp [gcdMoment]
  | succ e ih =>
      have hstep := gcdMoment_prime_pow_succ hp e k
      have htot : ((p ^ (e + 1)).totient : ℤ) = (p : ℤ) ^ e * ((p : ℤ) - 1) := by
        rw [Nat.totient_prime_pow hp (Nat.succ_pos e)]
        have h1 : 1 ≤ p := by omega
        push_cast [Nat.cast_sub h1]
        ring
      have hcast : (gcdMoment k (p ^ (e + 1)) : ℤ)
          = (p : ℤ) ^ k * (gcdMoment k (p ^ e) : ℤ) + (p : ℤ) ^ e * ((p : ℤ) - 1) := by
        rw [hstep]
        push_cast
        rw [htot]
      have hsum : ∑ i ∈ Finset.range (e + 1), (p : ℤ) ^ (i * k) *
            ((gcdMoment k p : ℤ) ^ (e + 1 - 1 - i) - (p : ℤ) ^ (e + 1 - 1 - i))
          = ((gcdMoment k p : ℤ) ^ e - (p : ℤ) ^ e)
            + (p : ℤ) ^ k * ∑ i ∈ Finset.range e, (p : ℤ) ^ (i * k) *
                ((gcdMoment k p : ℤ) ^ (e - 1 - i) - (p : ℤ) ^ (e - 1 - i)) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_sub_cancel, Nat.zero_mul, pow_zero, one_mul, Nat.sub_zero]
        rw [Finset.mul_sum, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hidx : e - (i + 1) = e - 1 - i := by omega
        rw [hidx, ← mul_assoc, ← pow_add]
        ring_nf
      rw [hcast, hsum, pow_succ]
      linear_combination ((p : ℤ) ^ k) * ih + (gcdMoment k p : ℤ) ^ e * hL

/-! ### The Euler product of the finest factorisation -/

/-- `Π_k(n) = ∏_{p ∈ primeFactorsList n} (p^k + p − 1)`: the moment predicted by the *finest*
factorisation of `n`, the prime factorisation counted with multiplicity. -/
-- [dropped: platform already declares primeProd]
@[simp] lemma primeProd_one (k : ℕ) : primeProd k 1 = 1 := by simp [primeProd]

@[simp] lemma primeProd_prime {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeProd k p = gcdMoment k p := by
  simp [primeProd, Nat.primeFactorsList_prime hp]

/-- **`Π_k` is completely multiplicative.** -/
theorem primeProd_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (k : ℕ) :
    primeProd k (a * b) = primeProd k a * primeProd k b := by
  have hperm := Nat.perm_primeFactorsList_mul ha hb
  unfold primeProd
  rw [(hperm.map (gcdMoment k)).prod_eq, List.map_append, List.prod_append]

theorem primeProd_prime_pow {p : ℕ} (hp : p.Prime) (e k : ℕ) :
    primeProd k (p ^ e) = gcdMoment k p ^ e := by
  simp [primeProd, hp.primeFactorsList_pow]

lemma primeProd_pos (n k : ℕ) : 0 < primeProd k n := by
  unfold primeProd
  refine List.prod_pos ?_
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
  have := gcdMoment_ge k p hpp.pos
  have : 0 < p ^ k := Nat.pow_pos hpp.pos
  omega

/-! ### The upper envelope -/

/-- **The upper envelope of the refinement order.**  For every modulus, the moment is at most
the Euler product of its prime factorisation. -/
theorem gcdMoment_le_primeProd {k : ℕ} (hk : 1 ≤ k) : ∀ {n : ℕ}, 0 < n →
    gcdMoment k n ≤ primeProd k n := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p e hp he =>
      intro _
      rw [primeProd_prime_pow hp e]
      exact gcdMoment_prime_pow_le hp hk e
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one => intro _; simp [gcdMoment]
  | coprime a b ha hb hab iha ihb =>
      intro _
      have ha0 : 0 < a := by omega
      have hb0 : 0 < b := by omega
      rw [gcdMoment_mul_of_coprime ha0 hb0 hab k, primeProd_mul ha0.ne' hb0.ne' k]
      exact Nat.mul_le_mul (iha ha0) (ihb hb0)

/-- On a squarefree modulus the moment *is* the full Euler product. -/
theorem gcdMoment_eq_primeProd_of_squarefree {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    gcdMoment k n = primeProd k n := by
  have hnodup : n.primeFactorsList.Nodup := hn.nodup_primeFactorsList
  have hlist : primeProd k n = ∏ p ∈ n.primeFactors, gcdMoment k p := by
    unfold primeProd
    rw [← Nat.toFinset_factors, List.prod_toFinset _ hnodup]
  rw [hlist, gcdMoment_squarefree hn k]
  refine Finset.prod_congr rfl fun p hp => ?_
  exact (gcdMoment_prime (Nat.prime_of_mem_primeFactors hp) k).symm

/-- **Strictness off the squarefree locus.** -/
theorem gcdMoment_lt_primeProd_of_not_squarefree {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n)
    (hsq : ¬ Squarefree n) : gcdMoment k n < primeProd k n := by
  obtain ⟨p, hp, hpp⟩ : ∃ p, p.Prime ∧ p ^ 2 ∣ n := by
    by_contra hcon
    push_neg at hcon
    refine hsq ?_
    rw [Nat.squarefree_iff_prime_squarefree]
    intro q hq hdvd
    exact hcon q hq (by simpa [pow_two] using hdvd)
  set e := n.factorization p with he
  have h2e : 2 ≤ e := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp hn.ne').1 hpp
    omega
  set m := n / p ^ e with hm
  have hsplit : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hm0 : 0 < m := Nat.ordCompl_pos p hn.ne'
  have hcop : Nat.Coprime (p ^ e) m := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn.ne')
  have hppos : 0 < p ^ e := Nat.pow_pos hp.pos
  have hlt : gcdMoment k (p ^ e) < primeProd k (p ^ e) := by
    rw [primeProd_prime_pow hp e]
    exact gcdMoment_prime_pow_lt hp hk h2e
  have hle : gcdMoment k m ≤ primeProd k m := gcdMoment_le_primeProd hk hm0
  have hmpos : 0 < gcdMoment k m := by
    have := gcdMoment_ge k m hm0
    have : 0 < m ^ k := Nat.pow_pos hm0
    omega
  calc gcdMoment k n = gcdMoment k (p ^ e) * gcdMoment k m := by
        rw [← hsplit, gcdMoment_mul_of_coprime hppos hm0 hcop k]
    _ < primeProd k (p ^ e) * primeProd k m := by
        exact Nat.mul_lt_mul_of_lt_of_le hlt hle (primeProd_pos m k)
    _ = primeProd k n := by rw [← primeProd_mul hppos.ne' hm0.ne' k, hsplit]

/-- **Equality holds exactly on the squarefree moduli.**  The moment equals the Euler product
of its prime factorisation iff `n` is squarefree; the deficiency `Π_k(n) − M_k(n)` is a strictly
positive measure of the square part. -/
theorem gcdMoment_eq_primeProd_iff_squarefree {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) :
    gcdMoment k n = primeProd k n ↔ Squarefree n := by
  constructor
  · intro heq
    by_contra hsq
    exact absurd heq (gcdMoment_lt_primeProd_of_not_squarefree hk hn hsq).ne
  · intro hsq
    exact gcdMoment_eq_primeProd_of_squarefree hsq k

/-! ### The refinement order is pinned at both ends -/

/-- The predicted Euler product of an arbitrary factorisation, given as a list of parts. -/
-- [dropped: platform already declares factorisationEuler]
lemma part_le_primeProd {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha : 0 < a) :
    a ^ k + a - 1 ≤ primeProd k a :=
  le_trans (gcdMoment_ge_local ha k) (gcdMoment_le_primeProd hk ha)

/-- **The prime factorisation maximises the predicted moment.**  For every factorisation of `n`
into parts `≥ 1`, the Euler product predicted by that factorisation is at most `Π_k(n)`.
With `eulerProd_ge_eulerLocal` of the previous cycle (the single-part factorisation is the
minimum) this pins the refinement order at both ends: the moment predicted by a factorisation
of `n` always lies in `[n^k + n − 1, Π_k(n)]`. -/
theorem factorisationEuler_le_primeProd {k : ℕ} (hk : 1 ≤ k) :
    ∀ (l : List ℕ), (∀ a ∈ l, 0 < a) → factorisationEuler k l ≤ primeProd k l.prod
  | [], _ => by simp [factorisationEuler]
  | (a :: t), h => by
      have ha : 0 < a := h a (by simp)
      have ht : ∀ x ∈ t, 0 < x := fun x hx => h x (by simp [hx])
      have hprod : 0 < t.prod := List.prod_pos ht
      have ih : factorisationEuler k t ≤ primeProd k t.prod :=
        factorisationEuler_le_primeProd hk t ht
      have hstep : a ^ k + a - 1 ≤ primeProd k a := part_le_primeProd hk ha
      have : factorisationEuler k (a :: t) = (a ^ k + a - 1) * factorisationEuler k t := by
        simp [factorisationEuler]
      rw [this, List.prod_cons, primeProd_mul ha.ne' hprod.ne' k]
      exact Nat.mul_le_mul hstep ih

/-- **The two-sided bracket.**  For `n ≥ 2` and `k ≥ 1`,
`n^k + n − 1 ≤ M_k(n) ≤ Π_k(n)`, the left equality characterising primes
(`gcdMoment_eq_local_iff_prime`) and the right one squarefreeness
(`gcdMoment_eq_primeProd_iff_squarefree`). -/
theorem gcdMoment_bracket {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 2 ≤ n) :
    n ^ k + n - 1 ≤ gcdMoment k n ∧ gcdMoment k n ≤ primeProd k n :=
  ⟨gcdMoment_ge_local (by omega) k, gcdMoment_le_primeProd hk (by omega)⟩

/-- The bracket collapses to a single point exactly at the primes: a prime is the only modulus
whose moment equals both ends. -/
theorem bracket_collapse_iff_prime {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 2 ≤ n) :
    (n ^ k + n - 1 = gcdMoment k n ∧ gcdMoment k n = primeProd k n) ↔ n.Prime := by
  constructor
  · rintro ⟨hleft, -⟩
    exact ((gcdMoment_eq_local_iff_prime hn hk).1 hleft.symm)
  · intro hp
    refine ⟨((gcdMoment_eq_local_iff_prime hn hk).2 hp).symm, ?_⟩
    rw [primeProd_prime hp]

/-! ### Lab notes: brute-force checks of the envelope

`M_2(4) = 22 < 25 = Π_2(4)`, `M_2(8) = 92 < 125`, `M_2(9) = 105 < 121`, while
`M_2(6) = 55 = Π_2(6)` and `M_3(30) = 33669 = Π_3(30)` (squarefree). -/

example : gcdMoment 2 4 = 22 := by decide
example : gcdMoment 2 4 < gcdMoment 2 2 ^ 2 := by decide
example : gcdMoment 2 8 = 92 := by decide
example : gcdMoment 2 8 < gcdMoment 2 2 ^ 3 := by decide
example : gcdMoment 2 9 < gcdMoment 2 3 ^ 2 := by decide
example : gcdMoment 2 6 = gcdMoment 2 2 * gcdMoment 2 3 := by decide
example : gcdMoment 2 12 = gcdMoment 2 4 * gcdMoment 2 3 := by decide
example : gcdMoment 2 9 + (3 - 1) * (3 ^ 2 - 1) = gcdMoment 2 3 ^ 2 := by decide
example : gcdMoment 3 4 + (2 - 1) * (2 ^ 3 - 1) = gcdMoment 3 2 ^ 2 := by decide

end GCDMoment
-- ==== upstream: Packages/Catalog/Novelty/GCDMomentFactorisationLattice.lean ====
/-!
# The factorisation lattice of a gcd moment: both extremes are attained *uniquely*

This is the fourth cycle of the gcd-moment project
(`Novelty.GCDMomentTraceWitness`, `Novelty.GCDMomentPairInversion`,
`Novelty.GCDMomentHigherInversion`, `Novelty.GCDMomentMultiplicative`,
`Novelty.GCDMomentRefinementOrder`).

Cycle 3 proved that the moment predicted by *any* factorisation `n = a_1 ⋯ a_r` into parts
`a_i ≥ 2`, namely

`E_k(a_1,…,a_r) = ∏_i (a_i^k + a_i − 1)`  (`factorisationEuler`),

lies in the bracket `[n^k + n − 1, Π_k(n)]`, where `Π_k(n)` is the value at the prime
factorisation (`primeProd`).  What was missing was *uniqueness* at the two ends.  This file
supplies it and draws the consequence for the inversion problem:

* `factorisationEuler_all_prime` — a factorisation into primes always predicts `Π_k(n)`.
* `factorisationEuler_lt_primeProd_of_mem_not_prime` — one composite part already makes the
  prediction *strictly* smaller than `Π_k(n)`.
* `factorisationEuler_eq_primeProd_iff_all_prime` — **the prime factorisation is the unique
  maximiser** of the predicted moment.
* `local_le_factorisationEuler`, `local_lt_factorisationEuler` — the natural-number form of the
  lower end, with strictness as soon as there are two parts: **the trivial factorisation `[n]` is
  the unique minimiser.**
* `collision_of_all_prime`, `collision_of_singleton` — consequently *no* collision of predicted
  moments can involve an extremal factorisation: if two factorisations of the same modulus
  predict the same moment and one of them is the prime factorisation (resp. the trivial
  factorisation), they agree up to order.
* `length_le_cardFactors`, `all_prime_of_cardFactors_le_length` — the combinatorial input: a
  factorisation into parts `≥ 2` has at most `Ω(n)` parts, with equality exactly when every part
  is prime.
* `no_collision_of_cardFactors_le_two` — **the capstone**: for every `k ≥ 1`, if `Ω(n) ≤ 2` then
  the predicted moment determines the factorisation up to order.  In particular
  `no_collision_semiprime`: on the semiprime moduli that the factoring question is about, *every*
  moment — including the ambiguous `k = 2` — is injective on factorisations.  Every collision
  (e.g. the `k = 2` collisions `2·14 = 4·7` at `N = 28` and `2·18 = 3·12` at `N = 36`) therefore
  needs `Ω(N) ≥ 3` and a composite part on *both* sides, which is exactly what those two
  examples show.
-/

namespace GCDMoment

open ArithmeticFunction

/-! ### Arithmetic of the natural-number Euler product -/

/-- A single local factor of a part `≥ 2` is at least `3`. -/
lemma three_le_part {a k : ℕ} (ha : 2 ≤ a) (hk : 1 ≤ k) : 3 ≤ a ^ k + a - 1 := by
  have : a ≤ a ^ k := Nat.le_self_pow (by omega) a
  omega

/-- A local factor of a part `≥ 1` is at least `1`. -/
lemma one_le_part {a k : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k) : 1 ≤ a ^ k + a - 1 := by
  have : a ≤ a ^ k := Nat.le_self_pow (by omega) a
  omega

@[simp] lemma factorisationEuler_nil (k : ℕ) : factorisationEuler k [] = 1 := by
  simp [factorisationEuler]

lemma factorisationEuler_cons (k a : ℕ) (t : List ℕ) :
    factorisationEuler k (a :: t) = (a ^ k + a - 1) * factorisationEuler k t := by
  simp [factorisationEuler]

lemma factorisationEuler_append (k : ℕ) (s t : List ℕ) :
    factorisationEuler k (s ++ t) = factorisationEuler k s * factorisationEuler k t := by
  simp [factorisationEuler, List.map_append, List.prod_append]

lemma factorisationEuler_pos {k : ℕ} (hk : 1 ≤ k) :
    ∀ {l : List ℕ}, (∀ a ∈ l, 1 ≤ a) → 0 < factorisationEuler k l
  | [], _ => by simp
  | (a :: t), h => by
      have ha : 1 ≤ a := h a (by simp)
      have ih : 0 < factorisationEuler k t :=
        factorisationEuler_pos hk (fun x hx => h x (by simp [hx]))
      have := one_le_part (a := a) (k := k) ha hk
      rw [factorisationEuler_cons]
      exact Nat.mul_pos (by omega) ih

/-! ### The lower end of the bracket, in `ℕ` -/

/-- Splitting one part strictly raises the predicted moment (natural-number form of
`eulerLocal_refine`). -/
lemma local_refine_nat {u v k : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) (hk : 1 ≤ k) :
    (u * v) ^ k + u * v - 1 < (u ^ k + u - 1) * (v ^ k + v - 1) := by
  have h := eulerLocal_refine (u := (u : ℤ)) (v := (v : ℤ))
    (by exact_mod_cast hu) (by exact_mod_cast hv) hk
  simp only [eulerLocal] at h
  have hu1 : 1 ≤ u ^ k + u := by
    have : 1 ≤ u ^ k := Nat.one_le_pow _ _ (by omega); omega
  have hv1 : 1 ≤ v ^ k + v := by
    have : 1 ≤ v ^ k := Nat.one_le_pow _ _ (by omega); omega
  have huv1 : 1 ≤ (u * v) ^ k + u * v := by
    have : 1 ≤ (u * v) ^ k := Nat.one_le_pow _ _ (by positivity); omega
  zify [hu1, hv1, huv1]
  linarith [h]

/-- **The lower end of the bracket.**  Any factorisation into parts `≥ 2` predicts at least the
local factor of the modulus. -/
theorem local_le_factorisationEuler {k : ℕ} (hk : 1 ≤ k) :
    ∀ (l : List ℕ), l ≠ [] → (∀ a ∈ l, 2 ≤ a) →
      l.prod ^ k + l.prod - 1 ≤ factorisationEuler k l
  | [], h, _ => absurd rfl h
  | [a], _, _ => by simp [factorisationEuler]
  | (a :: b :: t), _, h => by
      have ha : 2 ≤ a := h a (by simp)
      have hrest : 2 ≤ (b :: t).prod := by
        have hb : 2 ≤ b := h b (by simp)
        have : 1 ≤ t.prod := List.one_le_prod (fun x hx => by have := h x (by simp [hx]); omega)
        rw [List.prod_cons]
        calc 2 = 2 * 1 := by ring
          _ ≤ b * t.prod := Nat.mul_le_mul hb this
      have ih : (b :: t).prod ^ k + (b :: t).prod - 1 ≤ factorisationEuler k (b :: t) :=
        local_le_factorisationEuler hk (b :: t) (by simp) (fun x hx => h x (by simp [hx]))
      have hstep := local_refine_nat ha hrest hk
      have hpos : 0 < a ^ k + a - 1 := by have := three_le_part ha hk; omega
      calc (a :: b :: t).prod ^ k + (a :: b :: t).prod - 1
          = (a * (b :: t).prod) ^ k + a * (b :: t).prod - 1 := by rw [List.prod_cons]
        _ ≤ (a ^ k + a - 1) * ((b :: t).prod ^ k + (b :: t).prod - 1) := le_of_lt hstep
        _ ≤ (a ^ k + a - 1) * factorisationEuler k (b :: t) := Nat.mul_le_mul_left _ ih
        _ = factorisationEuler k (a :: b :: t) := (factorisationEuler_cons _ _ _).symm

/-- **The trivial factorisation is the unique minimiser.**  As soon as a factorisation has two
parts, its predicted moment strictly exceeds the local factor of the modulus. -/
theorem local_lt_factorisationEuler {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (t : List ℕ) (hne : t ≠ [])
    (h : ∀ x ∈ a :: t, 2 ≤ x) :
    (a :: t).prod ^ k + (a :: t).prod - 1 < factorisationEuler k (a :: t) := by
  have ha : 2 ≤ a := h a (by simp)
  have hrest : 2 ≤ t.prod := by
    obtain ⟨b, s, rfl⟩ : ∃ b s, t = b :: s := by
      cases t with
      | nil => exact absurd rfl hne
      | cons b s => exact ⟨b, s, rfl⟩
    have hb : 2 ≤ b := h b (by simp)
    have : 1 ≤ s.prod := List.one_le_prod (fun x hx => by have := h x (by simp [hx]); omega)
    rw [List.prod_cons]
    calc 2 = 2 * 1 := by ring
      _ ≤ b * s.prod := Nat.mul_le_mul hb this
  have ih : t.prod ^ k + t.prod - 1 ≤ factorisationEuler k t :=
    local_le_factorisationEuler hk t hne (fun x hx => h x (by simp [hx]))
  have hstep := local_refine_nat ha hrest hk
  have hpos : 0 < a ^ k + a - 1 := by have := three_le_part ha hk; omega
  calc (a :: t).prod ^ k + (a :: t).prod - 1
      = (a * t.prod) ^ k + a * t.prod - 1 := by rw [List.prod_cons]
    _ < (a ^ k + a - 1) * (t.prod ^ k + t.prod - 1) := hstep
    _ ≤ (a ^ k + a - 1) * factorisationEuler k t := Nat.mul_le_mul_left _ ih
    _ = factorisationEuler k (a :: t) := (factorisationEuler_cons _ _ _).symm

/-! ### The upper end of the bracket: uniqueness of the maximiser -/

/-- A factorisation into primes predicts exactly `Π_k(n)`. -/
theorem factorisationEuler_all_prime (k : ℕ) :
    ∀ (l : List ℕ), (∀ a ∈ l, a.Prime) → factorisationEuler k l = primeProd k l.prod
  | [], _ => by simp
  | (a :: t), h => by
      have ha : a.Prime := h a (by simp)
      have ht : ∀ x ∈ t, x.Prime := fun x hx => h x (by simp [hx])
      have hprod : 0 < t.prod := List.prod_pos (fun x hx => (ht x hx).pos)
      have ih : factorisationEuler k t = primeProd k t.prod := factorisationEuler_all_prime k t ht
      rw [factorisationEuler_cons, ih, List.prod_cons, primeProd_mul ha.pos.ne' hprod.ne',
        primeProd_prime ha, gcdMoment_prime ha]

/-- A single composite part strictly lowers the prediction below the maximum. -/
theorem factorisationEuler_lt_primeProd_of_mem_not_prime {k : ℕ} (hk : 1 ≤ k) {l : List ℕ}
    (h2 : ∀ a ∈ l, 2 ≤ a) {a : ℕ} (ha : a ∈ l) (hap : ¬ a.Prime) :
    factorisationEuler k l < primeProd k l.prod := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  have h2a : 2 ≤ a := h2 a (by simp)
  have hmem : ∀ x ∈ s ++ a :: t, 2 ≤ x := h2
  have h2s : ∀ x ∈ s, 2 ≤ x := fun x hx => hmem x (by simp [hx])
  have h2t : ∀ x ∈ t, 2 ≤ x := fun x hx => hmem x (by simp [hx])
  have hsp : 0 < s.prod := List.prod_pos (fun x hx => by have := h2s x hx; omega)
  have htp : 0 < t.prod := List.prod_pos (fun x hx => by have := h2t x hx; omega)
  -- the composite part is strictly below its own prime product
  have hstrict : a ^ k + a - 1 < primeProd k a := by
    have h1 := gcdMoment_gt_local_of_not_prime h2a hap hk
    have h2' := gcdMoment_le_primeProd hk (n := a) (by omega)
    omega
  have hs : factorisationEuler k s ≤ primeProd k s.prod :=
    factorisationEuler_le_primeProd hk s (fun x hx => by have := h2s x hx; omega)
  have ht : factorisationEuler k t ≤ primeProd k t.prod :=
    factorisationEuler_le_primeProd hk t (fun x hx => by have := h2t x hx; omega)
  have hsp' : 0 < factorisationEuler k s :=
    factorisationEuler_pos hk (fun x hx => by have := h2s x hx; omega)
  have htp' : 0 < factorisationEuler k t :=
    factorisationEuler_pos hk (fun x hx => by have := h2t x hx; omega)
  have hkey : factorisationEuler k s * ((a ^ k + a - 1) * factorisationEuler k t)
      < primeProd k s.prod * (primeProd k a * primeProd k t.prod) := by
    have h1 : (a ^ k + a - 1) * factorisationEuler k t < primeProd k a * primeProd k t.prod :=
      Nat.mul_lt_mul_of_lt_of_le hstrict ht (primeProd_pos t.prod k)
    exact Nat.mul_lt_mul_of_le_of_lt hs h1 (primeProd_pos s.prod k)
  have hprodeq : (s ++ a :: t).prod = s.prod * (a * t.prod) := by
    rw [List.prod_append, List.prod_cons]
  rw [factorisationEuler_append, factorisationEuler_cons, hprodeq,
    primeProd_mul hsp.ne' (by positivity) k, primeProd_mul (by omega) htp.ne' k]
  exact hkey

/-- **The prime factorisation is the unique maximiser of the predicted moment.** -/
theorem factorisationEuler_eq_primeProd_iff_all_prime {k : ℕ} (hk : 1 ≤ k) {l : List ℕ}
    (h2 : ∀ a ∈ l, 2 ≤ a) :
    factorisationEuler k l = primeProd k l.prod ↔ ∀ a ∈ l, a.Prime := by
  constructor
  · intro heq a ha
    by_contra hap
    exact absurd heq (factorisationEuler_lt_primeProd_of_mem_not_prime hk h2 ha hap).ne
  · intro h
    exact factorisationEuler_all_prime k l h

/-! ### No collision can involve an extremal factorisation -/

/-- If a factorisation into primes predicts the same moment as another factorisation of the same
modulus, the two agree up to order. -/
theorem collision_of_all_prime {k : ℕ} (hk : 1 ≤ k) {l m : List ℕ} (h2m : ∀ a ∈ m, 2 ≤ a)
    (hl : ∀ a ∈ l, a.Prime) (hprod : l.prod = m.prod)
    (heq : factorisationEuler k l = factorisationEuler k m) : l.Perm m := by
  have h2l : ∀ a ∈ l, 2 ≤ a := fun a ha => (hl a ha).two_le
  have hmax : factorisationEuler k m = primeProd k m.prod := by
    rw [← heq, factorisationEuler_all_prime k l hl, hprod]
  have hmp : ∀ a ∈ m, a.Prime := (factorisationEuler_eq_primeProd_iff_all_prime hk h2m).1 hmax
  have hpl := Nat.primeFactorsList_unique (n := l.prod) rfl hl
  have hpm := Nat.primeFactorsList_unique (n := m.prod) rfl hmp
  rw [hprod] at hpl
  exact hpl.trans hpm.symm

/-- If the trivial factorisation `[n]` predicts the same moment as another factorisation of `n`,
that other factorisation is `[n]` as well. -/
theorem collision_of_singleton {k : ℕ} (hk : 1 ≤ k) {n : ℕ} {l : List ℕ} (hn : 2 ≤ n)
    (h2 : ∀ a ∈ l, 2 ≤ a) (hprod : l.prod = n)
    (heq : factorisationEuler k [n] = factorisationEuler k l) : l = [n] := by
  cases l with
  | nil => simp at hprod; omega
  | cons a t =>
      cases t with
      | nil =>
          simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
          rw [hprod]
      | cons b s =>
          exfalso
          have hlt := local_lt_factorisationEuler hk a (b :: s) (by simp) h2
          rw [hprod] at hlt
          have : factorisationEuler k [n] = n ^ k + n - 1 := by simp [factorisationEuler]
          omega

/-! ### The combinatorics of the number of parts -/

/-- A factorisation into parts `≥ 2` has at most `Ω(n)` parts. -/
lemma length_le_cardFactors :
    ∀ (l : List ℕ), (∀ a ∈ l, 2 ≤ a) → l.length ≤ cardFactors l.prod
  | [], _ => by simp
  | (a :: t), h => by
      have ha : 2 ≤ a := h a (by simp)
      have ht : ∀ x ∈ t, 2 ≤ x := fun x hx => h x (by simp [hx])
      have htp : 0 < t.prod := List.prod_pos (fun x hx => by have := ht x hx; omega)
      have ih : t.length ≤ cardFactors t.prod := length_le_cardFactors t ht
      have h1 : 1 ≤ cardFactors a := by
        rw [cardFactors_apply]
        have : a.primeFactorsList ≠ [] := by
          simp only [ne_eq, Nat.primeFactorsList_eq_nil, not_or]
          omega
        exact List.length_pos_iff.2 this
      rw [List.prod_cons, cardFactors_mul (by omega) htp.ne']
      simp only [List.length_cons]
      omega

/-- Equality in `length_le_cardFactors` forces every part to be prime. -/
lemma all_prime_of_cardFactors_le_length :
    ∀ (l : List ℕ), (∀ a ∈ l, 2 ≤ a) → cardFactors l.prod ≤ l.length → ∀ a ∈ l, a.Prime
  | [], _, _ => by simp
  | (a :: t), h, hle => by
      have ha : 2 ≤ a := h a (by simp)
      have ht : ∀ x ∈ t, 2 ≤ x := fun x hx => h x (by simp [hx])
      have htp : 0 < t.prod := List.prod_pos (fun x hx => by have := ht x hx; omega)
      have hlent : t.length ≤ cardFactors t.prod := length_le_cardFactors t ht
      have h1 : 1 ≤ cardFactors a := by
        rw [cardFactors_apply]
        have : a.primeFactorsList ≠ [] := by
          simp only [ne_eq, Nat.primeFactorsList_eq_nil, not_or]
          omega
        exact List.length_pos_iff.2 this
      rw [List.prod_cons, cardFactors_mul (by omega) htp.ne'] at hle
      simp only [List.length_cons] at hle
      have hA : cardFactors a = 1 := by omega
      have hap : a.Prime := cardFactors_eq_one_iff_prime.1 hA
      have htle : cardFactors t.prod ≤ t.length := by omega
      have := all_prime_of_cardFactors_le_length t ht htle
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact hap
      · exact this x hx'

/-! ### The capstone: at most two prime factors ⟹ no collision at any `k` -/

/-- **No collision below three prime factors.**  For every `k ≥ 1`, if the modulus has at most
two prime factors counted with multiplicity, then the moment predicted by a factorisation
determines that factorisation up to order.  Equivalently: every collision of predicted moments
— such as the second-moment collisions `2·14 = 4·7` (`N = 28`) and `2·18 = 3·12` (`N = 36`) —
needs `Ω(N) ≥ 3`, and (by `collision_of_all_prime` and `collision_of_singleton`) a composite
part on both sides. -/
theorem no_collision_of_cardFactors_le_two {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 2 ≤ n)
    (hOmega : cardFactors n ≤ 2) {l m : List ℕ} (h2l : ∀ a ∈ l, 2 ≤ a) (h2m : ∀ a ∈ m, 2 ≤ a)
    (hl : l.prod = n) (hm : m.prod = n)
    (heq : factorisationEuler k l = factorisationEuler k m) : l.Perm m := by
  have hlen_l : l.length ≤ 2 := by
    have := length_le_cardFactors l h2l
    rw [hl] at this; omega
  have hlen_m : m.length ≤ 2 := by
    have := length_le_cardFactors m h2m
    rw [hm] at this; omega
  have hl0 : l ≠ [] := by
    intro h; rw [h] at hl; simp at hl; omega
  have hm0 : m ≠ [] := by
    intro h; rw [h] at hm; simp at hm; omega
  -- if either side has a single part, that part is `n` and the other side must match
  by_cases hl1 : l.length = 1
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl1
    have : a = n := by simpa using hl
    subst this
    have := collision_of_singleton hk hn h2m hm heq
    rw [this]
  by_cases hm1 : m.length = 1
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hm1
    have : a = n := by simpa using hm
    subst this
    have := collision_of_singleton hk hn h2l hl heq.symm
    rw [this]
  -- otherwise both sides have exactly two parts, hence `Ω(n) = 2` and all parts are prime
  have hl2 : l.length = 2 := by
    have : 1 ≤ l.length := List.length_pos_iff.2 hl0
    omega
  have hm2 : m.length = 2 := by
    have : 1 ≤ m.length := List.length_pos_iff.2 hm0
    omega
  have hpl : ∀ a ∈ l, a.Prime := by
    refine all_prime_of_cardFactors_le_length l h2l ?_
    rw [hl, hl2]; omega
  exact collision_of_all_prime hk h2m hpl (by rw [hl, hm]) heq

/-- **The semiprime case.**  On the moduli the factoring question is about — a product of two
primes — *every* moment `k ≥ 1` separates factorisations, including the `k = 2` moment that is
ambiguous in general. -/
theorem no_collision_semiprime {k : ℕ} (hk : 1 ≤ k) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {l m : List ℕ} (h2l : ∀ a ∈ l, 2 ≤ a) (h2m : ∀ a ∈ m, 2 ≤ a)
    (hl : l.prod = p * q) (hm : m.prod = p * q)
    (heq : factorisationEuler k l = factorisationEuler k m) : l.Perm m := by
  have hn : 2 ≤ p * q := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have hOmega : cardFactors (p * q) ≤ 2 := by
    rw [cardFactors_mul hp.pos.ne' hq.pos.ne', cardFactors_eq_one_iff_prime.2 hp,
      cardFactors_eq_one_iff_prime.2 hq]
  exact no_collision_of_cardFactors_le_two hk hn hOmega h2l h2m hl hm heq

/-! ### Lab notes: the two known collisions really do have three prime factors

`28 = 2·14 = 4·7` and `36 = 2·18 = 3·12` are the complete list of second-moment collisions
(`Novelty.GCDMomentPairInversion`).  Both moduli have `Ω ≥ 3`, and on each side of each
collision one part is composite — exactly as `no_collision_of_cardFactors_le_two`,
`collision_of_all_prime` and `collision_of_singleton` require. -/

example : factorisationEuler 2 [2, 14] = factorisationEuler 2 [4, 7] := by decide

example : factorisationEuler 2 [2, 18] = factorisationEuler 2 [3, 12] := by decide

example : cardFactors 28 = 3 := by
  rw [show (28 : ℕ) = 2 * (2 * 7) by norm_num,
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num)]

example : cardFactors 36 = 4 := by
  rw [show (36 : ℕ) = 2 * (2 * (3 * 3)) by norm_num,
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num),
    cardFactors_eq_one_iff_prime.2 (by norm_num)]

/-- The prime factorisation of `28` beats both of its two-part factorisations, and the trivial
factorisation loses to both: the bracket of cycle 3 is strict at the ends. -/
example : factorisationEuler 2 [28] < factorisationEuler 2 [2, 14] ∧
    factorisationEuler 2 [2, 14] < factorisationEuler 2 [2, 2, 7] := by decide

/-- The four factorisations of `28` and their predicted second moments: the two extremes are
attained exactly once, the middle value twice. -/
example : factorisationEuler 2 [28] = 811 ∧ factorisationEuler 2 [2, 14] = 1045 ∧
    factorisationEuler 2 [4, 7] = 1045 ∧ factorisationEuler 2 [2, 2, 7] = 1375 := by decide

end GCDMoment
section
open GCDMoment
open ArithmeticFunction

theorem solution {k : ℕ} (hk : 1 ≤ k) (a : ℕ) (t : List ℕ) (hne : t ≠ [])
    (h : ∀ x ∈ a :: t, 2 ≤ x) :
    (a :: t).prod ^ k + (a :: t).prod - 1 < factorisationEuler k (a :: t) := by
  first
  | exact GCDMoment.local_lt_factorisationEuler hk a t hne h
  | exact GCDMoment.local_lt_factorisationEuler
  | exact @GCDMoment.local_lt_factorisationEuler k hk a t hne h
  | apply GCDMoment.local_lt_factorisationEuler
  | exact GCDMoment.local_lt_factorisationEuler ..


end
