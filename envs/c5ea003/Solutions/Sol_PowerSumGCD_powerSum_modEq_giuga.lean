-- Prove2me | solution 1 for PowerSumGCD.powerSum_modEq_giuga
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:34:36.771264+00:00
-- url     : https://prove2.me/submissions/88dbdc02-80e4-4b56-aa8e-d791475a52f2

-- Sol generated from Novelty/PowerSumGCDGiuga.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Definitions.Def_Novelty_PowerSumGCDGeneral
import Theorems.Thm_PowerSumGCD_cast_powerSum
import Theorems.Thm_PowerSumGCD_exists_cofactor_of_squarefree
import Theorems.Thm_PowerSumGCD_modEq_of_forall_prime_modEq

/-!
# A Giuga-type closed form for the power sum modulo a squarefree modulus

The divisibility characterisation `prime_dvd_powerSum_iff` says *whether* a prime factor
divides `F(N,k) = ∑_{a=1}^{N} a^k`.  Here we pin down the exact residue: for squarefree
`N` and `k > 0`,

  `F(N,k) ≡ - ∑_{r prime, r ∣ N, (r-1) ∣ k}  N / r   (mod N)`.

This is the power-sum analogue of the von Staudt–Clausen / Giuga formula: modulo the
prime `r₀`, every summand `N/r` with `r ≠ r₀` dies (because `r₀ ∣ N/r` for squarefree
`N`), while the surviving term `N/r₀` cancels the Fermat contribution `-N/r₀` of the
`r₀`-block.  Specialising to `N = p` prime and `k = p-1` recovers Giuga's sum
`∑_{a=1}^{p-1} a^{p-1} ≡ -1 (mod p)`.

## Main results

* `dvd_div_of_ne_of_mem_primeFactors` : `r₀ ∣ N / r` for distinct primes of a squarefree `N`;
* `powerSum_modEq_giuga` : the closed form above (written additively in `ℕ`);
* `powerSum_prime_giuga` : `∑_{a=1}^{p} a^{p-1} + 1 ≡ 0 (mod p)` for `p` prime;
* `powerSum_giuga_iff_neg_one` : for squarefree `N`, `F(N,k) ≡ -1 (mod N)` exactly when the
  Giuga sum `∑_{(r-1) ∣ k} N/r` is `≡ 1 (mod N)`.
-/

open Finset

open PowerSumGCD

/-- For squarefree `N` and distinct primes `r₀ ≠ r` dividing `N`, we have `r₀ ∣ N / r`. -/
lemma dvd_div_of_ne_of_mem_primeFactors {N r₀ r : ℕ} (hN : Squarefree N) (hr₀ : r₀.Prime)
    (hr₀N : r₀ ∣ N) (hr : r ∈ N.primeFactors) (hne : r ≠ r₀) : r₀ ∣ N / r := by
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hrN : r ∣ N := Nat.dvd_of_mem_primeFactors hr
  obtain ⟨m, rfl⟩ := hrN
  rw [Nat.mul_div_cancel_left _ hrp.pos]
  rcases (Nat.Prime.dvd_mul hr₀).mp hr₀N with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr₀ hrp).mp h).symm hne
  · exact h





open PowerSumGCD in
theorem solution{N k : ℕ} (hN : Squarefree N) (hk : 0 < k) :
    powerSum N k + ∑ r ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k), N / r ≡ 0 [MOD N] := by
  classical
  refine modEq_of_forall_prime_modEq hN fun r₀ hr₀ hr₀N => ?_
  haveI : Fact r₀.Prime := ⟨hr₀⟩
  obtain ⟨m, hm, hr₀m⟩ := exists_cofactor_of_squarefree hN hr₀ hr₀N
  have hdivm : N / r₀ = m := by rw [hm, Nat.mul_div_cancel_left _ hr₀.pos]
  have hzero : ∀ r ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k), r ≠ r₀ →
      ((N / r : ℕ) : ZMod r₀) = 0 := by
    intro r hr hne
    exact (ZMod.natCast_eq_zero_iff _ _).mpr
      (dvd_div_of_ne_of_mem_primeFactors hN hr₀ hr₀N (Finset.mem_filter.mp hr).1 hne)
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have hF : ((powerSum N k : ℕ) : ZMod r₀)
      = (m : ZMod r₀) * (if (r₀ - 1) ∣ k then -1 else 0) := by
    rw [hm]; exact cast_powerSum r₀ m hk
  rw [hF]
  by_cases hdk : (r₀ - 1) ∣ k
  · have hmem : r₀ ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k) :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hr₀, hr₀N, hN.ne_zero⟩, hdk⟩
    have hsum : ∑ r ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k), ((N / r : ℕ) : ZMod r₀)
        = ((N / r₀ : ℕ) : ZMod r₀) :=
      Finset.sum_eq_single_of_mem r₀ hmem fun b hb hne => hzero b hb hne
    rw [hsum, hdivm, if_pos hdk]
    ring
  · have hsum : ∑ r ∈ N.primeFactors.filter (fun r => (r - 1) ∣ k), ((N / r : ℕ) : ZMod r₀)
        = 0 := by
      refine Finset.sum_eq_zero fun b hb => hzero b hb ?_
      rintro rfl
      exact hdk (Finset.mem_filter.mp hb).2
    rw [hsum, if_neg hdk]
    ring
