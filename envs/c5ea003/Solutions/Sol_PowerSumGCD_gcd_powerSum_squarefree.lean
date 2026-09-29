-- Prove2me | solution 1 for PowerSumGCD.gcd_powerSum_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:31:48.864735+00:00
-- url     : https://prove2.me/submissions/6a36ba64-fd15-4bf3-81f6-e2e4d5b011a5

-- Sol generated from Novelty/PowerSumGCDGeneral.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDCarmichael
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Definitions.Def_Novelty_PowerSumGCDGeneral
import Theorems.Thm_PowerSumGCD_exists_cofactor_of_squarefree
import Theorems.Thm_PowerSumGCD_gcd_eq_prod_primeFactors_filter
import Theorems.Thm_PowerSumGCD_prime_dvd_powerSum_iff

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
theorem solution{N k : ℕ} (hN : Squarefree N) (hk : 0 < k) :
    Nat.gcd (powerSum N k) N
      = ∏ r ∈ N.primeFactors.filter (fun r => ¬ (r - 1) ∣ k), r := by
  classical
  rw [gcd_eq_prod_primeFactors_filter _ _ hN]
  refine Finset.prod_congr (Finset.filter_congr fun r hr => ?_) fun _ _ => rfl
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hrN : r ∣ N := Nat.dvd_of_mem_primeFactors hr
  obtain ⟨m, hm, hrm⟩ := exists_cofactor_of_squarefree hN hrp hrN
  subst hm
  simpa using prime_dvd_powerSum_iff hrp hrm hk
