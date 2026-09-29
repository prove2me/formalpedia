-- Prove2me | solution 1 for PowerSumGCD.modEq_of_forall_prime_modEq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:33:14.041204+00:00
-- url     : https://prove2.me/submissions/db71680a-ba94-4d39-81e4-2c0af6b15487

-- Sol generated from Novelty/PowerSumGCDGeneral.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDCarmichael
import Definitions.Def_Novelty_PowerSumGCDGeneral

/-!
# The power-sum gcd for arbitrary squarefree moduli, and the first-hit exponent

The semiprime analysis of `Novelty.PowerSumGCDFactoring` and
`Novelty.PowerSumGCDCarmichael` is a shadow of a statement about *every* squarefree
modulus: for `k > 0`,

  `gcd(F(N,k), N) = ∏ { r prime, r ∣ N, (r-1) ∤ k }`.

So the power-sum gcd is a *spectral read-out* of the multiplicative orders in `N`:
it deletes exactly those primes `r` for which `k` is a multiple of `r - 1`.  Its trivial
locus is the multiples of the Carmichael exponent `λ(N) = lcm_{r ∣ N} (r-1)`, and the
power sum itself is periodic mod `N` with that period (Korselt's criterion in disguise).

## Main results

* `gcd_eq_prod_primeFactors_filter` : for squarefree `N`, `gcd(a,N)` is the product of the
  primes of `N` that divide `a`;
* `gcd_powerSum_squarefree` : the product formula displayed above;
* `carmichaelSF` and `gcd_powerSum_eq_one_iff_squarefree` : the trivial locus of the gcd
  is exactly the set of multiples of the Carmichael exponent;
* `modEq_of_forall_prime_modEq` and `powerSum_modEq_add_period_squarefree` : Korselt-type
  periodicity of the power sum for arbitrary squarefree moduli;
* `gcd_powerSum_eq_self_iff`, `gcd_powerSum_eq_self_of_lt_min`,
  `gcd_powerSum_lt_self_at_min` : the *first hit* of the semiprime search happens exactly
  at `k = min(p-1, q-1)`, which is the source of the `O(N^{3/2})` cost of the method.
-/

open Finset

open PowerSumGCD












open PowerSumGCD in
theorem solution{N x y : ℕ} (hN : Squarefree N)
    (h : ∀ r : ℕ, r.Prime → r ∣ N → x ≡ y [MOD r]) : x ≡ y [MOD N] := by
  classical
  have hprod : ∏ r ∈ N.primeFactors, r = N := Nat.prod_primeFactors_of_squarefree hN
  have key : ∀ s : Finset ℕ, s ⊆ N.primeFactors → x ≡ y [MOD ∏ r ∈ s, r] := by
    intro s
    induction s using Finset.induction with
    | empty => simp [Nat.ModEq, Nat.mod_one]
    | insert r s hrs ih =>
      intro hsub
      have hr : r.Prime := Nat.prime_of_mem_primeFactors (hsub (Finset.mem_insert_self r s))
      have hsub' : s ⊆ N.primeFactors := fun z hz => hsub (Finset.mem_insert_of_mem hz)
      have hcop : Nat.Coprime r (∏ z ∈ s, z) := by
        refine Nat.Coprime.prod_right fun z hz => ?_
        have hz' : z.Prime := Nat.prime_of_mem_primeFactors (hsub' hz)
        exact (Nat.coprime_primes hr hz').mpr (by rintro rfl; exact hrs hz)
      rw [Finset.prod_insert hrs]
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        ⟨h r hr (Nat.dvd_of_mem_primeFactors (hsub (Finset.mem_insert_self r s))), ih hsub'⟩
  have := key N.primeFactors (Finset.Subset.refl _)
  rwa [hprod] at this
