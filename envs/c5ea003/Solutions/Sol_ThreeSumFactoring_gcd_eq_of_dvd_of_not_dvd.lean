-- Prove2me | solution 1 for ThreeSumFactoring.gcd_eq_of_dvd_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:36.277462+00:00
-- url     : https://prove2.me/submissions/d7563497-28b8-4a94-afcc-cee18b3b88e3

-- Sol generated from Applications/ThreeSumFactoring.lean
import Mathlib
import Definitions.Def_Applications_ThreeSumFactoring
/-
# 3SUM mod `p` reveals a factor of `N = p*q`

Let `N = p * q` be a semiprime with `p ≠ q` two primes.  If a triple `(a,b,c)`
satisfies

* `a + b + c ≡ 0 (mod p)`, and
* `a + b + c ≢ 0 (mod q)`,

then `gcd(a+b+c, N) = p`: the triple *reveals* the factor `p`.

The file proves the general gcd lemma behind this observation, the 3SUM
specialisation, and a *guaranteed reveal* theorem which explains the experimental
observation that no small triple is ever divisible by both primes: any positive
sum smaller than `N` that is divisible by `p` is automatically **not** divisible
by `q`, hence always reveals `p`.  A concrete `N = 143 = 11 * 13` census is
verified by kernel computation.

Companion file: `Catalog/Applications/BirthdayBoundHierarchy.lean`, which shows
that the *cost* of finding such a triple obeys the same `√N` barrier as every
other collision-based factoring method.
-/

open ThreeSumFactoring

/-! ## The core arithmetic lemma -/



/-! ## The 3SUM specialisation -/





/-! ## Concrete census for `N = 143 = 11 * 13` -/






open ThreeSumFactoring in
theorem solution{p q s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hps : p ∣ s) (hqs : ¬ q ∣ s) : Nat.gcd s (p * q) = p := by
  set d := Nat.gcd s (p * q) with hd
  have hpd : p ∣ d := Nat.dvd_gcd hps (dvd_mul_right p q)
  have hdN : d ∣ p * q := Nat.gcd_dvd_right _ _
  obtain ⟨m, hm⟩ := hpd
  have hmq : m ∣ q := by
    have : p * m ∣ p * q := by rw [← hm]; exact hdN
    exact (mul_dvd_mul_iff_left hp.pos.ne').1 this
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq m hmq) with h1 | hq'
  · rw [hm, h1, mul_one]
  · exfalso
    apply hqs
    refine dvd_trans ?_ (Nat.gcd_dvd_left s (p * q))
    rw [← hd, hm, hq']
    exact dvd_mul_left q p
