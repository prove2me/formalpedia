-- Prove2me | solution 1 for RLHF.gibbs_vonMangoldt_apply
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:13:31.593561+00:00
-- url     : https://prove2.me/submissions/1a1dddfd-053e-4507-be86-c75019cefbe2

-- Sol generated from NumberTheory/RLHFPrimeDiscovery.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
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



theorem vmWeight_pos {β : ℝ} {N : ℕ} (i : Fin N) : 0 < vmWeight β N i := Real.exp_pos _

theorem sum_vmWeight_pos {β : ℝ} {N : ℕ} (hN : 0 < N) : 0 < ∑ i : Fin N, vmWeight β N i := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  exact Finset.sum_pos (fun i _ => vmWeight_pos i) univ_nonempty






open RLHF in
theorem solution{β : ℝ} {N : ℕ} (hN : 0 < N) (i : Fin N) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    gibbsPolicy β (vonMangoldtReward N) (unifRef N) i
      = vmWeight β N i / ∑ j : Fin N, vmWeight β N j := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hT : 0 < ∑ j : Fin N, vmWeight β N j := sum_vmWeight_pos hN
  have hpart : partition β (vonMangoldtReward N) (unifRef N)
      = (∑ j : Fin N, vmWeight β N j) / (N : ℝ) := by
    unfold partition unifRef vmWeight vonMangoldtReward
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  unfold gibbsPolicy
  rw [hpart]
  unfold unifRef vmWeight vonMangoldtReward
  field_simp
