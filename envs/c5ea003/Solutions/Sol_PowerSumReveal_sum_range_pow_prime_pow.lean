-- Prove2me | solution 1 for PowerSumReveal.sum_range_pow_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:58:14.25639+00:00
-- url     : https://prove2.me/submissions/618e00d2-c36a-4fde-a505-1c12beaa4cd4

-- Sol generated from Geometry/PowerSumPrimePower.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower
import Theorems.Thm_PowerSumReveal_sum_pow_zmod
import Theorems.Thm_PowerSumReveal_sum_pow_zmod_step
import Theorems.Thm_PowerSumReveal_sum_range_modCast

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
theorem solution(p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) {k : ℕ} (hk : k ≠ 0) :
    ∀ e : ℕ, 1 ≤ e →
      intPowerSum (p ^ e) k ≡ (if (p - 1) ∣ k then -(p : ℤ) ^ (e - 1) else 0) [ZMOD (p ^ e : ℕ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro e
  induction e with
  | zero => intro h; exact absurd h (by omega)
  | succ e ih =>
      intro _
      rcases Nat.eq_zero_or_pos e with rfl | he
      · -- base case `e = 1`: the classical Fermat power sum
        simp only [Nat.sub_self, pow_zero]
        have hbase : ((intPowerSum p k : ℤ) : ZMod p) = ((if (p - 1) ∣ k then -1 else 0 : ℤ) : ZMod p) := by
          rw [intPowerSum_cast p k, sum_range_modCast p (fun x => x ^ k), sum_pow_zmod p hk]
          split <;> push_cast <;> simp
        have := (ZMod.intCast_eq_intCast_iff _ _ _).1 hbase
        simpa using this
      · -- inductive step
        have he2 : 2 ≤ e + 1 := by omega
        have hstep : intPowerSum (p ^ (e + 1)) k ≡ (p : ℤ) * intPowerSum (p ^ e) k [ZMOD (p ^ (e + 1) : ℕ)] := by
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          refine (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_
          have h := sum_pow_zmod_step p (e + 1) k' hp hodd he2
          simp only [Nat.add_sub_cancel] at h
          rw [intPowerSum_cast (p ^ (e + 1)) (k' + 1)]
          push_cast
          rw [h]
          congr 1
          rw [intPowerSum]
          push_cast
          rfl
        have hIH := ih he
        have hmul : (p : ℤ) * intPowerSum (p ^ e) k
            ≡ (p : ℤ) * (if (p - 1) ∣ k then -(p : ℤ) ^ (e - 1) else 0)
              [ZMOD ((p : ℤ) * (p ^ e : ℕ))] := Int.ModEq.mul_left' hIH
        have hmod : ((p : ℤ) * (p ^ e : ℕ)) = ((p ^ (e + 1) : ℕ) : ℤ) := by
          push_cast; ring
        rw [hmod] at hmul
        have hval : (p : ℤ) * (if (p - 1) ∣ k then -(p : ℤ) ^ (e - 1) else 0)
            = (if (p - 1) ∣ k then -(p : ℤ) ^ (e + 1 - 1) else 0) := by
          have hee : e + 1 - 1 = (e - 1) + 1 := by omega
          rw [hee]
          split
          · rw [pow_succ]; ring
          · ring
        rw [hval] at hmul
        exact hstep.trans hmul
