-- Prove2me | solution 1 for RLHF.vonMangoldt_rewardMax
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:37:20.305345+00:00
-- url     : https://prove2.me/submissions/70524bd8-8644-4538-b0e1-1af28cdf8a7d

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum

/-!
# Zero- and infinite-temperature limits of the RLHF free energy

Continuing `NumberTheory.RLHFTemperatureSpectrum`, we quantify the two endpoints of the
free-energy spectrum `V(β) = β log Z(β)`:

* `RLHF.kl_budget` — the aligned policy cannot collapse: `β · KL(π_β ‖ p) ≤ max r − min r`.
* `RLHF.freeEnergy_ge_point` — `V(β) ≥ r y + β log p y` for every response `y`.
* `RLHF.tendsto_freeEnergy_zero_temperature` — as `β → 0⁺`, `V(β) → max r`
  (greedy reward maximization).
* `RLHF.freeEnergy_le_high_temperature` and `RLHF.tendsto_freeEnergy_high_temperature`
  — as `β → ∞`, `V(β) → 𝔼_p[r]` (the SFT reference), with the explicit rate
  `V(β) ≤ min r + e^{(max r − min r)/β} (𝔼_p[r] − min r)`.

Arithmetic payoff (`RLHF.vonMangoldt_zero_temperature_limit`): for the von Mangoldt reward
on `{1, …, N}` the zero-temperature limit of the RLHF free energy equals `log P` where `P`
is the **largest prime ≤ N**, while the infinite-temperature limit is the Chebyshev average
`ψ(N)/N`.  The whole alignment spectrum of this reward model is thus pinned between two
classical prime-counting quantities.
-/

open RLHF

open Finset ArithmeticFunction Filter Topology

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Pointwise lower bounds and the KL budget -/



/-! ## 2. The zero-temperature (greedy) limit -/


theorem le_rewardMax (r : Ω → ℝ) (y : Ω) : r y ≤ rewardMax r :=
  Finset.le_sup' r (mem_univ y)





/-! ## 3. The high-temperature (reference) limit -/



/-! ## 4. Arithmetic endpoint: the largest prime below `N` -/





open RLHF in
theorem solution{N : ℕ} (hN : 2 ≤ N) :
    ∃ P : ℕ, P.Prime ∧ P ≤ N ∧ (∀ q : ℕ, q.Prime → q ≤ N → q ≤ P) ∧
      haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
      rewardMax (vonMangoldtReward N) = Real.log P := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega : 0 < N)
  classical
  set S : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime with hS
  have h2S : 2 ∈ S := by
    simp [hS, Nat.prime_two]
    omega
  have hSne : S.Nonempty := ⟨2, h2S⟩
  set P := S.max' hSne with hP
  have hPmem : P ∈ S := S.max'_mem hSne
  have hPprime : P.Prime := by
    have := Finset.mem_filter.mp hPmem
    exact this.2
  have hPle : P ≤ N := by
    have := Finset.mem_filter.mp hPmem
    have := Finset.mem_range.mp this.1
    omega
  have hPmax : ∀ q : ℕ, q.Prime → q ≤ N → q ≤ P := by
    intro q hq hqN
    refine Finset.le_max' S q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩)
  have hP2 : 2 ≤ P := hPprime.two_le
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP2)
  refine ⟨P, hPprime, hPle, hPmax, le_antisymm ?_ ?_⟩
  · -- every reward value is at most `log P`
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    unfold vonMangoldtReward
    by_cases hpp : IsPrimePow ((i : ℕ) + 1)
    · have hval : Λ ((i : ℕ) + 1) = Real.log (Nat.minFac ((i : ℕ) + 1)) := by
        rw [vonMangoldt_apply, if_pos hpp]
      have hge2 : 2 ≤ (i : ℕ) + 1 := hpp.two_le
      have hne1 : ((i : ℕ) + 1) ≠ 1 := by omega
      have hmf : (Nat.minFac ((i : ℕ) + 1)).Prime := Nat.minFac_prime hne1
      have hmfle : Nat.minFac ((i : ℕ) + 1) ≤ N := by
        have h1 : Nat.minFac ((i : ℕ) + 1) ≤ (i : ℕ) + 1 := Nat.minFac_le (by omega)
        have h2 : (i : ℕ) + 1 ≤ N := i.isLt
        omega
      have := hPmax _ hmf hmfle
      rw [hval]
      apply Real.log_le_log (by exact_mod_cast hmf.pos)
      exact_mod_cast this
    · rw [vonMangoldt_apply, if_neg hpp]
      exact hlogP.le
  · -- the value `log P` is attained at the response `P`
    have hlt : P - 1 < N := by omega
    have hidx : ((⟨P - 1, hlt⟩ : Fin N) : ℕ) + 1 = P := by simp; omega
    have hval : vonMangoldtReward N ⟨P - 1, hlt⟩ = Real.log P := by
      unfold vonMangoldtReward
      rw [hidx, vonMangoldt_apply_prime hPprime]
    rw [← hval]
    exact le_rewardMax _ _
