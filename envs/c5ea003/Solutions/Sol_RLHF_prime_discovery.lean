-- Prove2me | solution 1 for RLHF.prime_discovery
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:17:41.321627+00:00
-- url     : https://prove2.me/submissions/63ac63ae-d998-4858-b496-4159f8c3bf68

-- Sol generated from NumberTheory/RLHFPrimeDiscovery.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFPrimeDiscovery
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_gibbs_vonMangoldt_apply
import Theorems.Thm_RLHF_sum_nonPrimePow_weight_le
import Theorems.Thm_RLHF_two_weight_ge

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
theorem solution{β : ℝ} {N : ℕ} (hN : 2 ≤ N) (hβ : 0 < β)
    (hthr : β * Real.log N ≤ Real.log 2) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
    (1 : ℝ) / 2
      ≤ ∑ i ∈ primePowerResponses N, gibbsPolicy β (vonMangoldtReward N) (unifRef N) i := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
  have hN0 : 0 < N := by omega
  set T := ∑ j : Fin N, vmWeight β N j with hT_def
  set S := ∑ i ∈ primePowerResponses N, vmWeight β N i with hS_def
  have hT : 0 < T := sum_vmWeight_pos hN0
  -- the aligned probability of the prime-power set is `S / T`
  have hprob : ∑ i ∈ primePowerResponses N, gibbsPolicy β (vonMangoldtReward N) (unifRef N) i
      = S / T := by
    rw [hS_def, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => gibbs_vonMangoldt_apply hN0 i)
  -- the response `2` lies in the prime-power set and carries weight ≥ N
  have hmem : (⟨1, by omega⟩ : Fin N) ∈ primePowerResponses N := by
    refine Finset.mem_filter.mpr ⟨mem_univ _, ?_⟩
    have : ((⟨1, by omega⟩ : Fin N) : ℕ) + 1 = 2 := by simp
    rw [this]
    exact Nat.prime_two.isPrimePow
  have hSge : (N : ℝ) ≤ S := by
    have hle : vmWeight β N ⟨1, by omega⟩ ≤ S :=
      Finset.single_le_sum (f := fun i => vmWeight β N i)
        (fun i _ => (vmWeight_pos i).le) hmem
    exact le_trans (two_weight_ge hN hβ hthr) hle
  -- split the total weight into prime powers and the rest
  have hsplit : T = S + ∑ i ∈ univ.filter (fun i : Fin N => ¬ IsPrimePow ((i : ℕ) + 1)),
      vmWeight β N i := by
    rw [hT_def, hS_def, primePowerResponses]
    exact (Finset.sum_filter_add_sum_filter_not univ
      (fun i : Fin N => IsPrimePow ((i : ℕ) + 1)) (fun i => vmWeight β N i)).symm
  have hrest := sum_nonPrimePow_weight_le (β := β) (N := N)
  have hTle : T ≤ 2 * S := by
    rw [hsplit]
    linarith
  have hSpos : 0 < S := lt_of_lt_of_le (by exact_mod_cast hN0) hSge
  rw [hprob, le_div_iff₀ hT]
  linarith
