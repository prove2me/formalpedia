-- Prove2me | solution 1 for PowerSumReveal.sum_pow_zmod_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:45.326862+00:00
-- url     : https://prove2.me/submissions/55e322c4-df24-45f1-a847-412cb96c4b34

-- Sol generated from Geometry/PowerSumPrimePower.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPrimePower

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

/-- Splitting a range of length `M * t` into `t` blocks of length `M`. -/
theorem sum_range_block {R : Type*} [AddCommMonoid R] (M : ℕ) (f : ℕ → R) (t : ℕ) :
    ∑ a ∈ range (M * t), f a = ∑ j ∈ range t, ∑ r ∈ range M, f (M * j + r) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h : M * (t + 1) = M * t + M := by ring
      rw [h, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Binomial expansion when the increment squares to zero. -/
theorem add_pow_of_sq_eq_zero {R : Type*} [CommRing R] (x y : R) (hy : y ^ 2 = 0) (k : ℕ) :
    (x + y) ^ (k + 1) = x ^ (k + 1) + (k + 1) * x ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h : (x + y) ^ (k + 2) = (x + y) ^ (k + 1) * (x + y) := by ring
      rw [h, ih]; push_cast; linear_combination ((k : R) + 1) * x ^ k * hy

/-! ## Lifting the exponent -/


/-! ## The prime-power Fermat sum -/




/-! ## Consequences for the power sum -/






open PowerSumReveal in
theorem solution(p e k' : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (he : 2 ≤ e) :
    (∑ a ∈ range (p ^ e), (a : ZMod (p ^ e)) ^ (k' + 1))
      = (p : ZMod (p ^ e)) * ∑ r ∈ range (p ^ (e - 1)), (r : ZMod (p ^ e)) ^ (k' + 1) := by
  obtain ⟨c, hc⟩ : ∃ c, p - 1 = 2 * c := by
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hodd
    exact ⟨m, by omega⟩
  set M := p ^ (e - 1) with hM
  have hMe : M * p = p ^ e := by
    rw [hM, ← pow_succ]; congr 1; omega
  have hMsq : ((M : ZMod (p ^ e))) ^ 2 = 0 := by
    have hd : (p : ℕ) ^ e ∣ M ^ 2 := by
      rw [hM, ← pow_mul]; exact pow_dvd_pow p (by omega)
    have h := (ZMod.natCast_eq_zero_iff (M ^ 2) (p ^ e)).2 hd
    push_cast at h
    exact h
  have hMp : (M : ZMod (p ^ e)) * (p : ZMod (p ^ e)) = 0 := by
    have h : ((M * p : ℕ) : ZMod (p ^ e)) = 0 := by
      rw [hMe]; exact (ZMod.natCast_eq_zero_iff _ _).2 dvd_rfl
    push_cast at h; exact h
  have hgauss : ∑ i ∈ range p, i = p * c := by
    have h2 := Finset.sum_range_id_mul_two p
    have h3 : p * (p - 1) = 2 * (p * c) := by rw [hc]; ring
    omega
  have key : ∀ j ∈ range p, ∑ r ∈ range M, ((M * j + r : ℕ) : ZMod (p ^ e)) ^ (k' + 1)
      = (∑ r ∈ range M, (r : ZMod (p ^ e)) ^ (k' + 1))
        + (((k' : ZMod (p ^ e)) + 1) * (∑ r ∈ range M, (r : ZMod (p ^ e)) ^ k'))
          * ((M : ZMod (p ^ e)) * j) := by
    intro j _
    have hy : ((M : ZMod (p ^ e)) * j) ^ 2 = 0 := by
      have h : ((M : ZMod (p ^ e)) * j) ^ 2
          = (M : ZMod (p ^ e)) ^ 2 * (j : ZMod (p ^ e)) ^ 2 := by ring
      rw [h, hMsq, zero_mul]
    have hterm : ∀ r ∈ range M, ((M * j + r : ℕ) : ZMod (p ^ e)) ^ (k' + 1)
        = (r : ZMod (p ^ e)) ^ (k' + 1)
          + ((k' : ZMod (p ^ e)) + 1) * (r : ZMod (p ^ e)) ^ k' * ((M : ZMod (p ^ e)) * j) := by
      intro r _
      push_cast
      rw [add_comm ((M : ZMod (p ^ e)) * j) (r : ZMod (p ^ e))]
      exact add_pow_of_sq_eq_zero (r : ZMod (p ^ e)) ((M : ZMod (p ^ e)) * j) hy k'
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum]
  calc ∑ a ∈ range (p ^ e), (a : ZMod (p ^ e)) ^ (k' + 1)
      = ∑ j ∈ range p, ∑ r ∈ range M, ((M * j + r : ℕ) : ZMod (p ^ e)) ^ (k' + 1) := by
        rw [← hMe, sum_range_block]
    _ = ∑ _j ∈ range p, ((∑ r ∈ range M, (r : ZMod (p ^ e)) ^ (k' + 1))
          + (((k' : ZMod (p ^ e)) + 1) * (∑ r ∈ range M, (r : ZMod (p ^ e)) ^ k'))
            * ((M : ZMod (p ^ e)) * _j)) := Finset.sum_congr rfl key
    _ = (p : ZMod (p ^ e)) * ∑ r ∈ range M, (r : ZMod (p ^ e)) ^ (k' + 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have hj : ∑ i ∈ range p, (i : ZMod (p ^ e)) = ((p * c : ℕ) : ZMod (p ^ e)) := by
          rw [← hgauss]; push_cast; rfl
        have hzero : (M : ZMod (p ^ e)) * ((p * c : ℕ) : ZMod (p ^ e)) = 0 := by
          push_cast; rw [← mul_assoc, hMp, zero_mul]
        rw [hj, hzero, mul_zero, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
