-- Prove2me | solution 1 for Bridges.AlexanderTorus.torusAlexander_semiprime_natDegree_factors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:06:18.296984+00:00
-- url     : https://prove2.me/submissions/9767b511-7441-4423-8bf3-c557a7460d03

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII
open Polynomial Finset Bridges.AlexanderTorus in
theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) :
    torusAlexander p q = cyclotomic (p * q) ℤ ∧
      (torusAlexander p q).natDegree = (p - 1) * (q - 1) := by
  -- the only divisor of `pq` dividing neither `p` nor `q` is `pq` itself
  have hidx : torusIdx p q = {p * q} := by
    unfold torusIdx
    rw [Nat.divisors_mul, hp.divisors, hq.divisors]
    ext d
    simp only [mem_sdiff, mem_union, mem_singleton, mem_insert, Finset.mem_mul]
    constructor
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, hnot⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd (Or.inl (Or.inl (by ring))) hnot
      · exact absurd (Or.inr (Or.inr (by ring))) hnot
      · exact absurd (Or.inl (Or.inr (by ring))) hnot
      · rfl
    · rintro rfl
      refine ⟨⟨p, Or.inr rfl, q, Or.inr rfl, rfl⟩, ?_⟩
      have hp1 := hp.one_lt
      have hq1 := hq.one_lt
      rintro ((h | h) | (h | h))
      · nlinarith
      · have : q = 1 := by
          have := Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_one p).symm)
          exact this
        omega
      · nlinarith
      · have : p = 1 := by
          have := Nat.eq_of_mul_eq_mul_right hq.pos (h.trans (one_mul q).symm)
          exact this
        omega
  have hcyc : torusAlexander p q = cyclotomic (p * q) ℤ := by
    unfold torusAlexander
    rw [hidx, prod_singleton]
  refine ⟨hcyc, ?_⟩
  rw [hcyc, natDegree_cyclotomic, Nat.totient_mul ((Nat.coprime_primes hp hq).2 hne),
    Nat.totient_prime hp, Nat.totient_prime hq]
