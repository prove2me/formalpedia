-- Prove2me | solution 2 for Round10.freeWitness_odd_eq_totient_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T01:09:15.723715+00:00
-- url     : https://prove2.me/submissions/b77c7275-f094-45c5-ba34-1d3622c26451

-- Sol generated from Geometry/Round10Closures/CarmichaelThreshold.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_freeWitness_odd
import Theorems.Thm_Round10_prod_eq_prod_of_le
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





/-- The local totients multiply to `φ(N)`. -/
theorem prod_totient_prime_pow {N : ℕ} (hN : N ≠ 0) :
    ∏ p ∈ N.primeFactors, Nat.totient (p ^ N.factorization p) = Nat.totient N := by
  rw [Nat.totient_eq_prod_factorization hN, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact Nat.totient_prime_pow hpp
    (hpp.factorization_pos_of_dvd hN (Nat.dvd_of_mem_primeFactors hp))




open Round10 in
theorem solution{N : ℕ} (hodd : Odd N) (hN : N ≠ 0) (k : ℕ) :
    freeWitness N k = Nat.totient N ↔
      ∀ p ∈ N.primeFactors, Nat.totient (p ^ N.factorization p) ∣ k := by
  classical
  rw [freeWitness_odd hodd hN k, ← prod_totient_prime_pow hN]
  constructor
  · intro h p hp
    have hpos : ∀ i ∈ N.primeFactors, 0 < Nat.totient (i ^ N.factorization i) := fun i hi =>
      Nat.totient_pos.mpr (pow_pos (Nat.prime_of_mem_primeFactors hi).pos _)
    have hgcd : (Nat.totient (p ^ N.factorization p)).gcd k
        = Nat.totient (p ^ N.factorization p) :=
      prod_eq_prod_of_le N.primeFactors
        (fun i => (Nat.totient (i ^ N.factorization i)).gcd k)
        (fun i => Nat.totient (i ^ N.factorization i))
        (fun i hi => Nat.gcd_le_left _ (hpos i hi)) hpos h p hp
    rw [← hgcd]
    exact Nat.gcd_dvd_right _ _
  · intro h
    exact Finset.prod_congr rfl fun p hp => Nat.gcd_eq_left (h p hp)
