-- Prove2me | solution 1 for PowerSumReveal.gcd_powerSum_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:04:36.954555+00:00
-- url     : https://prove2.me/submissions/c601b8a3-be5e-4f87-81de-e7e184d0add8

-- Sol generated from Geometry/PowerSumPrimePower.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower
import Theorems.Thm_PowerSumReveal_powerSum_prime_pow_cast
import Theorems.Thm_PowerSumReveal_powerSum_prime_pow_not_dvd

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


/-- If `(p-1) ∤ k` then the *whole* prime power `p^e ‖ N` divides the power sum. -/
theorem powerSum_prime_pow_dvd {p e m k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hk : k ≠ 0) (hdk : ¬ (p - 1) ∣ k) : p ^ e ∣ powerSum (p ^ e * m) k := by
  have h := powerSum_prime_pow_cast p e m hp hodd he hk (k := k)
  rw [if_neg hdk, mul_zero] at h
  have hz : ((p ^ e : ℕ) : ℤ) ∣ ((powerSum (p ^ e * m) k : ℕ) : ℤ) :=
    Int.modEq_zero_iff_dvd.1 h
  exact_mod_cast hz




open PowerSumReveal in
theorem solution{p e m k : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    (hk : k ≠ 0) (hm : ¬ p ∣ m) :
    Nat.gcd (powerSum (p ^ e * m) k) (p ^ e)
      = if (p - 1) ∣ k then p ^ (e - 1) else p ^ e := by
  by_cases hdk : (p - 1) ∣ k
  · rw [if_pos hdk]
    obtain ⟨hlow, hhigh⟩ := powerSum_prime_pow_not_dvd hp hodd he hk hdk hm
    have hg : Nat.gcd (powerSum (p ^ e * m) k) (p ^ e) ∣ p ^ e := Nat.gcd_dvd_right _ _
    obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow hp).1 hg
    have hle : p ^ (e - 1) ∣ Nat.gcd (powerSum (p ^ e * m) k) (p ^ e) :=
      Nat.dvd_gcd hlow (pow_dvd_pow p (by omega))
    have hine : i ≠ e := by
      intro hie
      have hd : Nat.gcd (powerSum (p ^ e * m) k) (p ^ e) ∣ powerSum (p ^ e * m) k :=
        Nat.gcd_dvd_left _ _
      rw [hgi, hie] at hd
      exact hhigh hd
    have hige : e - 1 ≤ i := by
      rw [hgi] at hle
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hle
    have : i = e - 1 := by omega
    rw [hgi, this]
  · rw [if_neg hdk]
    exact Nat.gcd_eq_right (powerSum_prime_pow_dvd hp hodd he hk hdk)
