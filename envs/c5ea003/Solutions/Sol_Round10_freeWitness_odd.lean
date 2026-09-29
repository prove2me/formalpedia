-- Prove2me | solution 1 for Round10.freeWitness_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:50:37.7453+00:00
-- url     : https://prove2.me/submissions/7a1954ef-ba59-41a1-9218-ba860c429d36

-- Sol generated from Geometry/Round10Closures/CarmichaelThreshold.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_freeWitness_prod_coprime
import Theorems.Thm_Round10_rootCount_of_isCyclic
/-
Round-10 Closures — Part IX (cycle 5): the aggregation depth of an arbitrary odd modulus.

Cycle 4 identified the exact aggregation depth of the free-witness channel for semiprimes
and for squarefree moduli: the least exponent with a maximal witness is `lcm_{r ∣ N}(r-1)`.
Cycle 5 removes the squarefree hypothesis on the odd part: for *every* odd `N`,

    R_k(N) = ∏_{p ∣ N} gcd(φ(p^{v_p(N)}), k),

and the least positive exponent with `R_k(N) = φ(N)` is the Carmichael exponent
`λ(N) = lcm_{p ∣ N} φ(p^{v_p(N)})`.

The only input beyond the previous cycles is the cyclicity of `(ZMod (p^e))ˣ` for odd
primes; the `2`-adic case is genuinely different (the local group is not cyclic for
`8 ∣ N`) and is left open.
-/

open Round10


/-- The local witness at an odd prime power: the unit group is cyclic, so the count is the
gcd of the exponent with `φ(p^n)`. -/
theorem freeWitness_prime_pow_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n k : ℕ) :
    freeWitness (p ^ n) k = (Nat.totient (p ^ n)).gcd k := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
  rw [freeWitness, rootCount_of_isCyclic, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

/-- Every prime factor of an odd number is odd. -/
theorem ne_two_of_mem_primeFactors_odd {N p : ℕ} (hodd : Odd N) (hp : p ∈ N.primeFactors) :
    p ≠ 2 := by
  rintro rfl
  have h2 : (2 : ℕ) ∣ N := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.odd_iff] at hodd
  omega






open Round10 in
theorem solution{N : ℕ} (hodd : Odd N) (hN : N ≠ 0) (k : ℕ) :
    freeWitness N k = ∏ p ∈ N.primeFactors, (Nat.totient (p ^ N.factorization p)).gcd k := by
  classical
  have hdecomp : ∏ p ∈ N.primeFactors, p ^ N.factorization p = N := by
    have := Nat.factorization_prod_pow_eq_self hN
    rwa [Finsupp.prod, Nat.support_factorization] at this
  calc freeWitness N k
      = freeWitness (∏ p ∈ N.primeFactors, p ^ N.factorization p) k := by rw [hdecomp]
    _ = ∏ p ∈ N.primeFactors, freeWitness (p ^ N.factorization p) k := by
        refine freeWitness_prod_coprime k _ _ fun a ha b hb hab => ?_
        exact Nat.Coprime.pow _ _
          ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
            (Nat.prime_of_mem_primeFactors hb)).mpr hab)
    _ = ∏ p ∈ N.primeFactors, (Nat.totient (p ^ N.factorization p)).gcd k :=
        Finset.prod_congr rfl fun p hp =>
          freeWitness_prime_pow_odd (Nat.prime_of_mem_primeFactors hp)
            (ne_two_of_mem_primeFactors_odd hodd hp) _ k
