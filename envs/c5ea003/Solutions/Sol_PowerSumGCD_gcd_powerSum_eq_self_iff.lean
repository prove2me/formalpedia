-- Prove2me | solution 1 for PowerSumGCD.gcd_powerSum_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:31:48.064756+00:00
-- url     : https://prove2.me/submissions/2daf4c47-bcd4-4ace-a7bd-e3de8ae67d71

-- Sol generated from Novelty/PowerSumGCDGeneral.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDCarmichael
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Definitions.Def_Novelty_PowerSumGCDGeneral
import Theorems.Thm_PowerSumGCD_gcd_powerSum_semiprime

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
theorem solution{p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hk : 0 < k) :
    Nat.gcd (powerSum (p * q) k) (p * q) = p * q ↔ (¬ (p - 1) ∣ k ∧ ¬ (q - 1) ∣ k) := by
  rw [gcd_powerSum_semiprime hp hq hpq hk]
  constructor
  · intro h
    by_cases h1 : (p - 1) ∣ k <;> by_cases h2 : (q - 1) ∣ k
    · rw [if_pos h1, if_pos h2, one_mul] at h
      exact absurd h.symm (by
        have := hp.one_lt; have := hq.one_lt; nlinarith)
    · rw [if_pos h1, if_neg h2, one_mul] at h
      exact absurd h (by have := hp.one_lt; have := hq.pos; nlinarith)
    · rw [if_neg h1, if_pos h2, mul_one] at h
      exact absurd h (by have := hq.one_lt; have := hp.pos; nlinarith)
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [if_neg h1, if_neg h2]
