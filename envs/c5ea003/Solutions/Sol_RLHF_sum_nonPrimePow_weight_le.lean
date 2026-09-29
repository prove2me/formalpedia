-- Prove2me | solution 1 for RLHF.sum_nonPrimePow_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:15:18.665661+00:00
-- url     : https://prove2.me/submissions/98bc7845-4371-4945-811e-0bcc4e72ad48

-- Sol generated from NumberTheory/RLHFPrimeDiscovery.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPrimeDiscovery
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

/-!
# Reward hacking finds the primes: a quantitative low-temperature theorem

Take the response space `{1, …, N}`, the uniform SFT reference, and the von Mangoldt
reward `Λ`.  The aligned (Gibbs) policy then has the explicit arithmetic form

`π_β(n) ∝ e^{Λ(n)/β} = p^{1/β}` if `n = p^k` is a prime power, and `∝ 1` otherwise.

**Main theorem** (`RLHF.prime_discovery`): as soon as the KL coefficient satisfies
`β log N ≤ log 2`, the aligned policy emits a **prime power** with probability at least
`1/2`.  In other words, a neurosymbolic reward built from the von Mangoldt function
provably drives the aligned model onto the primes once the KL leash is short enough — a
quantitative form of "reward hacking discovers arithmetic structure".

Supporting results: `RLHF.gibbs_vonMangoldt_apply` (closed form of the aligned policy),
`RLHF.sum_nonPrimePow_weight_le` (the non-prime-power mass is at most `N`), and
`RLHF.two_weight_ge` (the response `2` alone already carries weight `≥ N`).
-/

open RLHF

open Finset ArithmeticFunction










open RLHF in
theorem solution{β : ℝ} {N : ℕ} :
    ∑ i ∈ univ.filter (fun i : Fin N => ¬ IsPrimePow ((i : ℕ) + 1)), vmWeight β N i
      ≤ (N : ℝ) := by
  have hone : ∀ i ∈ univ.filter (fun i : Fin N => ¬ IsPrimePow ((i : ℕ) + 1)),
      vmWeight β N i = 1 := by
    intro i hi
    have hnp : ¬ IsPrimePow ((i : ℕ) + 1) := (Finset.mem_filter.mp hi).2
    unfold vmWeight
    rw [vonMangoldt_eq_zero_iff.mpr hnp]
    simp
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (univ.filter (fun i : Fin N => ¬ IsPrimePow ((i : ℕ) + 1))).card ≤ N := by
    have := Finset.card_filter_le (univ : Finset (Fin N))
      (fun i : Fin N => ¬ IsPrimePow ((i : ℕ) + 1))
    simpa using this
  exact_mod_cast hcard
