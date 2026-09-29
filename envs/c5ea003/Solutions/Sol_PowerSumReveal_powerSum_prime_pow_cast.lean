-- Prove2me | solution 1 for PowerSumReveal.powerSum_prime_pow_cast
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:59:56.849582+00:00
-- url     : https://prove2.me/submissions/bc7302e3-9bdf-4ae6-9ec7-05b5868da4c3

-- Sol generated from Geometry/PowerSumPrimePower.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower
import Theorems.Thm_PowerSumReveal_powerSum_cast
import Theorems.Thm_PowerSumReveal_sum_range_modCast
import Theorems.Thm_PowerSumReveal_sum_range_pow_prime_pow

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


lemma intPowerSum_cast (M k : ℕ) [NeZero M] :
    ((intPowerSum M k : ℤ) : ZMod M) = ∑ a ∈ range M, (a : ZMod M) ^ k := by
  unfold intPowerSum
  push_cast
  rfl


/-! ## Consequences for the power sum -/






open PowerSumReveal in
theorem solution(p e m : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (he : 1 ≤ e)
    {k : ℕ} (hk : k ≠ 0) :
    ((powerSum (p ^ e * m) k : ℕ) : ℤ)
      ≡ (m : ℤ) * (if (p - 1) ∣ k then -(p : ℤ) ^ (e - 1) else 0) [ZMOD (p ^ e : ℕ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
  have h1 : ((powerSum (p ^ e * m) k : ℕ) : ZMod (p ^ e))
      = (m : ZMod (p ^ e)) * ∑ x : ZMod (p ^ e), x ^ k := powerSum_cast (p ^ e) m hk
  have h2 : ∑ x : ZMod (p ^ e), x ^ k = ∑ a ∈ range (p ^ e), (a : ZMod (p ^ e)) ^ k :=
    (sum_range_modCast (p ^ e) (fun x => x ^ k)).symm
  have h3 : ((intPowerSum (p ^ e) k : ℤ) : ZMod (p ^ e))
      = ((if (p - 1) ∣ k then -(p : ℤ) ^ (e - 1) else 0 : ℤ) : ZMod (p ^ e)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).2 (sum_range_pow_prime_pow p hp hodd hk e he)
  rw [intPowerSum_cast (p ^ e) k] at h3
  push_cast at h1 h3 ⊢
  rw [h1, h2, h3]
