-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_lb_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:28:16.739517+00:00
-- url     : https://prove2.me/submissions/dc20b02d-f691-462d-8c05-3df3b7aa96a8

-- Sol generated from Shared/CyclicTypeChannelOdd.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
import Theorems.Thm_CyclicTypeChannel_Ipair_prime
/-
# Odd cyclic orders above the one-bit cap

The exact-value files show the type-pair channel `Ipair n` breaking the one-bit
binary-fork cap at `n = 4, 6, 8, 10, 12, 16`, and staying below it at the odd
orders `3, 5, 9, 15` (`odd_orders_below_cap`).  That coincidence suggested that
the order-two element of the cyclic group is what pushes the channel above the
cap.  This file **refutes** that reading:

`one_lt_Ipair_odd_order` exhibits an explicit **odd** cyclic order

  `M = 9 · 5 · 7 · 11 · 13 · 17 · 19 · 23 · 29 · 31 = 300840735195`

with `1 < Ipair M`.  So the cap is broken by odd orders too; evenness is not the
mechanism.  What *is* the mechanism is CRT additivity (`Ipair_mul_of_coprime`)
together with the fact that every prime-order channel is strictly positive: the
channel of a squarefree-ish odd order is a *sum* of small positive prime
contributions.  The accumulation is *tight*: the prime-order values decay like
`Ipair p ≈ (log₂ p + 2/ln 2)/p²`, so the total over all odd prime powers
converges (numerically to `≈ 1.084`), and the ten primary parts used here
already give `1.0052…` — no odd order can exceed `1.09`, and only a long tail of
primes gets past `1` at all.

The proof is a chain of three ingredients, all already formal:

* `Ipair_prime` — the closed form for a prime cyclic order;
* `Ipair_val_9` — the exact value of the prime-power order `9`;
* `Ipair_mul_of_coprime` — CRT additivity.

Each prime contribution is bounded below by an explicit rational number obtained
from integer inequalities `2 ^ a ≤ x ^ 4096` and `x ^ 4096 ≤ 2 ^ c`
(`logb_ge_of_pow_le`, `logb_le_of_le_pow`); summing the ten bounds gives
`Ipair M ≥ 1.0052… > 1`.
-/

open CyclicTypeChannel

set_option exponentiation.threshold 100000

/-! ## 1. Rational bounds for binary logarithms -/

/-- If `2 ^ a ≤ x ^ b` then `a / b ≤ log₂ x`: a rational lower bound for a binary
logarithm, certified by an integer inequality. -/
lemma logb_ge_of_pow_le {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b)
    (h : (2 : ℝ) ^ a ≤ x ^ b) : (a : ℝ) / (b : ℝ) ≤ Real.logb 2 x := by
  have h1 : Real.logb 2 ((2 : ℝ) ^ a) ≤ Real.logb 2 (x ^ b) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).2 h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hb']
  nlinarith [h1]

/-- If `x ^ b ≤ 2 ^ a` then `log₂ x ≤ a / b`. -/
lemma logb_le_of_le_pow {x : ℝ} (hx : 0 < x) {a b : ℕ} (hb : 0 < b)
    (h : x ^ b ≤ (2 : ℝ) ^ a) : Real.logb 2 x ≤ (a : ℝ) / (b : ℝ) := by
  have h1 : Real.logb 2 (x ^ b) ≤ Real.logb 2 ((2 : ℝ) ^ a) :=
    (Real.logb_le_logb (by norm_num) (by positivity) (by positivity)).2 h
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h1
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  nlinarith [h1]

/-! ## 2. Explicit rational lower bounds for the odd prime-order channels

Each bound is the closed form `Ipair_prime` evaluated with the two-sided
rational bounds of Section 1 at denominator `4096`. -/











/-! ## 3. An odd cyclic order above the one-bit cap -/





open CyclicTypeChannel in
lemma solution: (14083 / 591872 : ℝ) ≤ Ipair 17 := by
  have h := Ipair_prime (p := 17) (by norm_num)
  push_cast at h
  norm_num at h
  have h1 : ((16742 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 17 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  have h2 : Real.logb 2 16 ≤ ((16384 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) :=
    logb_le_of_le_pow (by norm_num) (by norm_num) (by norm_num)
  have h3 : ((16002 : ℕ) : ℝ) / ((4096 : ℕ) : ℝ) ≤ Real.logb 2 15 :=
    logb_ge_of_pow_le (by norm_num) (by norm_num) (by norm_num)
  push_cast at h1 h2 h3
  rw [h]
  linarith
