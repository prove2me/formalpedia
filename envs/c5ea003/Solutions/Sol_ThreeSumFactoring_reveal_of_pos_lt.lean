-- Prove2me | solution 1 for ThreeSumFactoring.reveal_of_pos_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:40:39.411322+00:00
-- url     : https://prove2.me/submissions/b3547b3b-de03-4fd9-838b-a1e466b93d3a

-- Sol generated from Applications/ThreeSumFactoring.lean
import Mathlib
import Definitions.Def_Applications_ThreeSumFactoring
import Theorems.Thm_ThreeSumFactoring_gcd_eq_of_dvd_of_not_dvd
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


/-- **No sum below `N` is divisible by both primes.**  This is the structural
reason the experimental "mod-both" census is always empty for small triples. -/
theorem not_dvd_both_of_lt {p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h0 : 0 < s) (hlt : s < p * q) : ¬ (p ∣ s ∧ q ∣ s) := by
  rintro ⟨h1, h2⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have : p * q ∣ s := hcop.mul_dvd_of_dvd_of_dvd h1 h2
  exact absurd (Nat.le_of_dvd h0 this) (not_le.2 hlt)



/-! ## Concrete census for `N = 143 = 11 * 13` -/






open ThreeSumFactoring in
theorem solution{p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h0 : 0 < s) (hlt : s < p * q) (hps : p ∣ s) : Nat.gcd s (p * q) = p := by
  refine gcd_eq_of_dvd_of_not_dvd hp hq hps (fun hqs => ?_)
  exact not_dvd_both_of_lt hp hq hpq h0 hlt ⟨hps, hqs⟩
