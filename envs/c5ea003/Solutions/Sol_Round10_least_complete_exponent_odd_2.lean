-- Prove2me | solution 2 for Round10.least_complete_exponent_odd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:14:56.865096+00:00
-- url     : https://prove2.me/submissions/1fdb1acd-8cd1-493b-b93a-6b71fd42e06e

import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
open Round10 Finset ArithmeticFunction in
theorem solution {N : ℕ} (hodd : Odd N) (hN : N ≠ 0) :
    IsLeast {m : ℕ | 0 < m ∧ freeWitness N m = Nat.totient N}
      (N.primeFactors.lcm fun p => Nat.totient (p ^ N.factorization p)) := by
  -- the full count is reached exactly at the common multiples of the `φ(p^e)`
  have hiff : ∀ k : ℕ, freeWitness N k = Nat.totient N ↔
      ∀ p ∈ N.primeFactors, Nat.totient (p ^ N.factorization p) ∣ k := by
    intro k
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
  have hl0 : 0 < N.primeFactors.lcm fun p => Nat.totient (p ^ N.factorization p) := by
    refine Nat.pos_of_ne_zero (fun h => ?_)
    obtain ⟨p, hp, h0⟩ := Finset.lcm_eq_zero_iff.1 h
    have hpp := Nat.prime_of_mem_primeFactors hp
    have := Nat.totient_pos.2 (pow_pos hpp.pos (N.factorization p))
    omega
  refine ⟨⟨hl0, (hiff _).2 (fun p hp => Finset.dvd_lcm hp)⟩, ?_⟩
  rintro m ⟨hm0, hm⟩
  exact Nat.le_of_dvd hm0 (Finset.lcm_dvd ((hiff m).1 hm))
