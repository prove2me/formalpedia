-- Prove2me | solution 1 for PowerSumReveal.powerSum_prime_pow_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:42.848701+00:00
-- url     : https://prove2.me/submissions/76fad87b-b98d-4015-827e-92bf7e906602

-- Sol generated from Geometry/PowerSumPrimePower.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower
import Theorems.Thm_PowerSumReveal_powerSum_prime_pow_cast

/-!
# Cycle 3: the power-sum reveal at a prime power

The squarefree theory of `Geometry.PowerSumSquarefree` rests on the Fermat evaluation
`∑_{x : ZMod p} x^k = -1` (if `(p-1) ∣ k`) or `0`.  This file removes the squarefreeness
restriction at odd primes by proving the prime-power analogue

`∑_{a < p^e} a^k ≡ -p^{e-1} (mod p^e)` if `(p-1) ∣ k`, and `≡ 0 (mod p^e)` otherwise,

for every odd prime `p`, every `e ≥ 1` and every `k ≥ 1`.  Note the exponent: the
condition is `(p-1) ∣ k`, **not** `λ(p^e) = p^{e-1}(p-1) ∣ k`; the extra `p`-part of the
unit group plays no role.  (Numerically: for `p^e = 9` the sum is `≡ 6 = -3` for every
even `k`, not only for `k` divisible by `6`.)

The proof is an induction on `e` using the "lift the exponent" step

`∑_{a < p^e} a^k ≡ p · ∑_{a < p^{e-1}} a^k (mod p^e)`,

obtained by writing `a = p^{e-1} j + r` and expanding binomially: the square of
`p^{e-1}` vanishes mod `p^e`, and the linear term carries the Gauss sum
`∑_{j<p} j = p(p-1)/2`, which is divisible by `p` precisely because `p` is odd.

Consequences: for `N = p^e * m` with `p ∤ m`,

`gcd (powerSum N k, p^e) = if (p-1) ∣ k then p^{e-1} else p^e`,

so a prime power `p^e ‖ N` is revealed in full unless `(p-1) ∣ k`, in which case exactly
one power of `p` is lost.  This is the correct generalisation of the semiprime master
formula to non-squarefree moduli.

## Main results

* `PowerSumReveal.sum_range_pow_prime_pow` — the prime-power Fermat sum.
* `PowerSumReveal.powerSum_prime_pow_dvd` / `powerSum_prime_pow_not_dvd`.
* `PowerSumReveal.gcd_powerSum_prime_pow` — the prime-power master formula.
-/

open PowerSumReveal

open Finset

/-! ## Two elementary tools -/



/-! ## Lifting the exponent -/


/-! ## The prime-power Fermat sum -/




/-! ## Consequences for the power sum -/






open PowerSumReveal in
theorem solution{p e m k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hk : k ≠ 0) (hdk : (p - 1) ∣ k) (hm : ¬ p ∣ m) :
    p ^ (e - 1) ∣ powerSum (p ^ e * m) k ∧ ¬ p ^ e ∣ powerSum (p ^ e * m) k := by
  have h := powerSum_prime_pow_cast p e m hp hodd he hk (k := k)
  rw [if_pos hdk] at h
  have hdvd : ((p ^ e : ℕ) : ℤ) ∣ ((powerSum (p ^ e * m) k : ℕ) : ℤ)
      + (m : ℤ) * (p : ℤ) ^ (e - 1) := by
    have h1 := Int.ModEq.dvd h.symm
    have h2 : ((powerSum (p ^ e * m) k : ℕ) : ℤ) - (m : ℤ) * -(p : ℤ) ^ (e - 1)
        = ((powerSum (p ^ e * m) k : ℕ) : ℤ) + (m : ℤ) * (p : ℤ) ^ (e - 1) := by ring
    rwa [h2] at h1
  constructor
  · -- `p^{e-1}` divides the sum
    have hple : ((p ^ (e - 1) : ℕ) : ℤ) ∣ ((p ^ e : ℕ) : ℤ) := by
      push_cast
      exact pow_dvd_pow (p : ℤ) (by omega)
    have h3 : ((p ^ (e - 1) : ℕ) : ℤ) ∣ ((powerSum (p ^ e * m) k : ℕ) : ℤ) := by
      have h4 : ((p ^ (e - 1) : ℕ) : ℤ) ∣ (m : ℤ) * (p : ℤ) ^ (e - 1) := by
        push_cast
        exact Dvd.intro_left _ rfl
      have h5 := dvd_trans hple hdvd
      exact (dvd_add_right h4).mp (by rwa [add_comm] at h5)
    exact_mod_cast h3
  · -- but `p^e` does not
    intro hcon
    have hcon' : ((p ^ e : ℕ) : ℤ) ∣ ((powerSum (p ^ e * m) k : ℕ) : ℤ) := by exact_mod_cast hcon
    have hfin : ((p ^ e : ℕ) : ℤ) ∣ (m : ℤ) * (p : ℤ) ^ (e - 1) :=
      (dvd_add_right hcon').mp hdvd
    have hnat : p ^ e ∣ m * p ^ (e - 1) := by exact_mod_cast hfin
    have hsplit : p ^ e = p ^ (e - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hsplit] at hnat
    have hnat' : p ^ (e - 1) * p ∣ p ^ (e - 1) * m := by
      rwa [mul_comm (p ^ (e - 1)) m]
    have hpos : 0 < p ^ (e - 1) := pow_pos hp.pos _
    exact hm ((mul_dvd_mul_iff_left hpos.ne').mp hnat')
