-- Prove2me | solution 1 for Round10.least_complete_exponent_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:54:56.460829+00:00
-- url     : https://prove2.me/submissions/08a8ab32-650c-4ec0-9871-6378161a0371

-- Sol generated from Geometry/Round10Closures/CarmichaelThreshold.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_freeWitness_odd_eq_totient_iff
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









open Round10 in
theorem solution{N : ℕ} (hodd : Odd N) (hN : N ≠ 0) :
    IsLeast {m : ℕ | 0 < m ∧ freeWitness N m = Nat.totient N}
      (N.primeFactors.lcm fun p => Nat.totient (p ^ N.factorization p)) := by
  classical
  have hpos : 0 < N.primeFactors.lcm fun p => Nat.totient (p ^ N.factorization p) := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [Finset.lcm_eq_zero_iff] at h0
    obtain ⟨p, hp, hp0⟩ := h0
    have : 0 < Nat.totient (p ^ N.factorization p) :=
      Nat.totient_pos.mpr (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
    omega
  refine ⟨⟨hpos, (freeWitness_odd_eq_totient_iff hodd hN _).mpr fun p hp => Finset.dvd_lcm hp⟩, ?_⟩
  rintro m ⟨hm, hcomp⟩
  exact Nat.le_of_dvd hm
    (Finset.lcm_dvd fun p hp => (freeWitness_odd_eq_totient_iff hodd hN m).mp hcomp p hp)
