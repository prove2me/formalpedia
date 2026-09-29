-- Prove2me | solution 1 for RLHF.freeEnergy_le_high_temperature
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:42.5371+00:00
-- url     : https://prove2.me/submissions/3764afc6-eb68-44c0-a0d8-f3da68101460

-- Sol generated from NumberTheory/RLHFTemperatureLimits.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFTemperatureLimits
import Definitions.Def_NumberTheory_RLHFTemperatureSpectrum
import Theorems.Thm_RLHF_partition_pos

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







/-! ## 3. The high-temperature (reference) limit -/



/-! ## 4. Arithmetic endpoint: the largest prime below `N` -/





open RLHF in
theorem solution{β m M : ℝ} {r p : Ω → ℝ} (hβ : 0 < β)
    (hp : IsPosDist p) (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) :
    freeEnergy β r p ≤ m + Real.exp ((M - m) / β) * ((∑ y, p y * r y) - m) := by
  set C := Real.exp ((M - m) / β) with hC
  set E := ∑ y, p y * r y with hE
  have hCpos : 0 < C := Real.exp_pos _
  have hEm : m ≤ E := by
    have hterm : ∀ y ∈ (univ : Finset Ω), p y * m ≤ p y * r y :=
      fun y _ => mul_le_mul_of_nonneg_left (hm y) (hp.1 y).le
    have := Finset.sum_le_sum hterm
    rwa [← Finset.sum_mul, hp.2, one_mul] at this
  -- pointwise bound `exp (r y / β) ≤ exp (m/β) (1 + ((r y - m)/β) C)`
  have hpt : ∀ y, Real.exp (r y / β)
      ≤ Real.exp (m / β) * (1 + ((r y - m) / β) * C) := by
    intro y
    have hu0 : 0 ≤ (r y - m) / β := div_nonneg (by linarith [hm y]) hβ.le
    have huM : (r y - m) / β ≤ (M - m) / β := by
      have h1 : r y - m ≤ M - m := by linarith [hM y]
      gcongr
    have hkey : Real.exp ((r y - m) / β) ≤ 1 + ((r y - m) / β) * Real.exp ((r y - m) / β) := by
      have h := Real.add_one_le_exp (-((r y - m) / β))
      rw [Real.exp_neg] at h
      have hpos : 0 < Real.exp ((r y - m) / β) := Real.exp_pos _
      have h2 := mul_le_mul_of_nonneg_left h hpos.le
      rw [mul_inv_cancel₀ (ne_of_gt hpos)] at h2
      nlinarith
    have hmono : Real.exp ((r y - m) / β) ≤ C := Real.exp_le_exp.mpr huM
    have h1 : Real.exp ((r y - m) / β) ≤ 1 + ((r y - m) / β) * C := by
      nlinarith
    have hexpand : Real.exp (r y / β) = Real.exp (m / β) * Real.exp ((r y - m) / β) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [hexpand]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hZ : partition β r p ≤ Real.exp (m / β) * (1 + ((E - m) / β) * C) := by
    have hsum : partition β r p
        ≤ ∑ y, p y * (Real.exp (m / β) * (1 + ((r y - m) / β) * C)) := by
      unfold partition
      exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hpt y) (hp.1 y).le)
    refine le_trans hsum (le_of_eq ?_)
    have hsplit : ∀ y ∈ (univ : Finset Ω),
        p y * (Real.exp (m / β) * (1 + ((r y - m) / β) * C))
          = Real.exp (m / β) * p y
            + (Real.exp (m / β) * C / β) * (p y * r y)
            - (Real.exp (m / β) * C * m / β) * p y := by
      intro y _
      field_simp
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, ← hE]
    field_simp
    ring
  have hW : 0 < 1 + ((E - m) / β) * C := by
    have : 0 ≤ ((E - m) / β) * C := mul_nonneg (div_nonneg (by linarith) hβ.le) hCpos.le
    linarith
  have hlogZ : Real.log (partition β r p) ≤ m / β + ((E - m) / β) * C := by
    have h1 : Real.log (partition β r p)
        ≤ Real.log (Real.exp (m / β) * (1 + ((E - m) / β) * C)) :=
      Real.log_le_log (partition_pos hp) hZ
    rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hW), Real.log_exp] at h1
    have h2 : Real.log (1 + ((E - m) / β) * C) ≤ ((E - m) / β) * C := by
      have := Real.log_le_sub_one_of_pos hW
      linarith
    linarith
  have hfin := mul_le_mul_of_nonneg_left hlogZ hβ.le
  have hcalc : β * (m / β + ((E - m) / β) * C) = m + C * (E - m) := by
    field_simp
  unfold freeEnergy
  linarith [hcalc ▸ hfin]
