-- Prove2me | solution 1 for RLHF.two_weight_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:15:19.289121+00:00
-- url     : https://prove2.me/submissions/5f152f2b-b6db-4525-a723-3011d5e07dec

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
theorem solution{β : ℝ} {N : ℕ} (hN : 2 ≤ N) (hβ : 0 < β)
    (hthr : β * Real.log N ≤ Real.log 2) :
    (N : ℝ) ≤ vmWeight β N ⟨1, by omega⟩ := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hval : vmWeight β N ⟨1, by omega⟩ = Real.exp (Real.log 2 / β) := by
    unfold vmWeight
    have h2 : Λ 2 = Real.log 2 := by simpa using vonMangoldt_apply_prime Nat.prime_two
    norm_num [h2]
  have hlog : Real.log N ≤ Real.log 2 / β := by
    rw [le_div_iff₀ hβ]
    linarith [hthr]
  have := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hNR, ← hval] at this
