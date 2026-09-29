-- Prove2me | solution 1 for Round10.freeWitness_odd_eq_totient_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:20:34.649583+00:00
-- url     : https://prove2.me/submissions/10e83a71-021b-4173-9603-47cd14d222cd

import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
open Round10 Finset ArithmeticFunction in
theorem solution {N : ℕ} (hodd : Odd N) (hN : N ≠ 0) (k : ℕ) :
    freeWitness N k = Nat.totient N ↔
      ∀ p ∈ N.primeFactors, Nat.totient (p ^ N.factorization p) ∣ k := by
  haveI : NeZero N := ⟨hN⟩
  have hcard : Nat.card (ZMod N)ˣ = Nat.totient N := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  -- the count is the whole unit group iff every unit is a `k`-th root of unity
  have hall : freeWitness N k = Nat.totient N ↔ ∀ x : (ZMod N)ˣ, x ^ k = 1 := by
    rw [← hcard, freeWitness, rootCount]
    constructor
    · intro h x
      by_contra hx
      have : Nat.card {y : (ZMod N)ˣ // y ^ k = 1} < Nat.card (ZMod N)ˣ :=
        Finite.card_subtype_lt hx
      omega
    · intro h
      exact Nat.card_congr (Equiv.subtypeUnivEquiv h)
  -- Carmichael: the exponent of `(ZMod N)ˣ` is the lcm of `φ(p^e)` over odd prime powers
  have hcar : carmichael N = N.primeFactors.lcm (fun p => Nat.totient (p ^ N.factorization p)) := by
    rw [carmichael_factorization]
    refine Finset.lcm_congr rfl (fun p hp => ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))
    exact carmichael_pow_of_prime_ne_two _ hpp hp2
  rw [hall, ← Monoid.exponent_dvd_iff_forall_pow_eq_one, ← carmichael_eq_exponent hN, hcar,
    Finset.lcm_dvd_iff]
