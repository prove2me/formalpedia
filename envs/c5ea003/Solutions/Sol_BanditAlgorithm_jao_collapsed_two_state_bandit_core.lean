-- Prove2me | solution 1 for BanditAlgorithm.jao_collapsed_two_state_bandit_core
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T17:32:50.711347+00:00
-- url     : https://prove2.me/submissions/2fece1c9-ff73-4838-b996-2e406df4a3eb

import Theorems.Thm_BanditAlgorithm_jao_two_state_gadget_optimal_gain_ge
import Theorems.Thm_BanditAlgorithm_jao_two_state_gadget_reward_le_reference_plus_planted_plays
import Theorems.Thm_BanditAlgorithm_jao_two_state_reference_occupancy_bounds
import Theorems.Thm_BanditAlgorithm_jao_two_state_planted_plays_change_of_measure
import Theorems.Thm_BanditAlgorithm_jao_collapsed_bandit_regret_arithmetic

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

namespace JaoCore

/-- The two-state gadget of JAO Figure 3 with escape bonus `e b` on action `b`:
state `0` is `s∘` (reward `0`), state `1` is `s_p` (reward `1`), the return
probability from `s_p` is `δ` for every action, and the escape probability from
`s∘` under action `b` is `δ + e b`. -/
noncomputable def G (m : ℕ) (δ : ℝ) (e : Fin m → ℝ)
    (h1 : 0 ≤ δ) (h2 : δ ≤ 1) (h3 : ∀ b, 0 ≤ δ + e b) (h4 : ∀ b, δ + e b ≤ 1) :
    FiniteMDP 2 m where
  P := fun s b s' =>
    if s = 0 then
      (if s' = 0 then Real.toNNReal (1 - (δ + e b)) else Real.toNNReal (δ + e b))
    else
      (if s' = 0 then Real.toNNReal δ else Real.toNNReal (1 - δ))
  P_sum_one := by
    intro s b
    rw [Fin.sum_univ_two]
    fin_cases s
    · apply NNReal.coe_injective
      show (Real.toNNReal (1 - (δ + e b)) : ℝ) + (Real.toNNReal (δ + e b) : ℝ) = 1
      rw [Real.coe_toNNReal _ (by linarith [h4 b]), Real.coe_toNNReal _ (h3 b)]
      ring
    · apply NNReal.coe_injective
      show (Real.toNNReal δ : ℝ) + (Real.toNNReal (1 - δ) : ℝ) = 1
      rw [Real.coe_toNNReal _ h1, Real.coe_toNNReal _ (by linarith)]
      ring
  r := fun s _ => if s = 0 then 0 else 1
  r_mem_Icc := by
    intro s _
    by_cases hs : s = 0 <;> simp [hs]

variable {m : ℕ} {δ : ℝ} {e : Fin m → ℝ}
  {h1 : 0 ≤ δ} {h2 : δ ≤ 1} {h3 : ∀ b, 0 ≤ δ + e b} {h4 : ∀ b, δ + e b ≤ 1}

lemma G_r0 (b : Fin m) : (G m δ e h1 h2 h3 h4).r 0 b = 0 := rfl

lemma G_r1 (b : Fin m) : (G m δ e h1 h2 h3 h4).r 1 b = 1 := rfl

lemma G_P1 (b : Fin m) : ((G m δ e h1 h2 h3 h4).P 1 b 0 : ℝ) = δ :=
  Real.coe_toNNReal _ h1

lemma G_P0 (b : Fin m) : ((G m δ e h1 h2 h3 h4).P 0 b 1 : ℝ) = δ + e b :=
  Real.coe_toNNReal _ (h3 b)

end JaoCore

open JaoCore

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ m : ℕ, 20 ≤ m → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 3 →
        ∀ T : ℕ, (16 : ℝ) * m ≤ δ * T →
          ∀ π : MDPPolicy 2 m,
            ∃ (a : Fin m) (ε : ℝ) (M : FiniteMDP 2 m),
              0 < ε ∧ ε ≤ δ ∧
              (∀ b, M.r 0 b = 0) ∧ (∀ b, M.r 1 b = 1) ∧
              (∀ b, (M.P 1 b 0 : ℝ) = δ) ∧
              (∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) ∧
              c * Real.sqrt ((T : ℝ) * m / δ) ≤
                ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac 0) π T) := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro m hm δ hδ0 hδ T hT π
  have hm0 : (0 : ℝ) < m := by
    have : (20 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hT0 : (0 : ℝ) < T := by
    by_cases h : (T : ℝ) ≤ 0
    · nlinarith
    · linarith [not_le.mp h]
  -- the choice of `ε`
  set ε : ℝ := 1 / 5 * Real.sqrt (δ * m / T) with hεdef
  have hquot : 0 < δ * m / T := by positivity
  have hε0 : 0 < ε := by
    have := Real.sqrt_pos.mpr hquot
    simp only [hεdef]; linarith
  have hεδ : ε ≤ δ := by
    have hkey : δ * m / T ≤ (5 * δ) ^ 2 := by
      rw [div_le_iff₀ hT0]
      nlinarith [mul_le_mul_of_nonneg_left hT (le_of_lt hδ0)]
    have := Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq (by linarith)] at this
    simp only [hεdef]; linarith
  have hδ1 : δ ≤ 1 := by linarith
  -- the reference gadget and the planted gadgets
  have h3z : ∀ b : Fin m, 0 ≤ δ + (0 : Fin m → ℝ) b := by intro b; simpa using hδ0.le
  have h4z : ∀ b : Fin m, δ + (0 : Fin m → ℝ) b ≤ 1 := by intro b; simpa using hδ1
  set M₀ : FiniteMDP 2 m := G m δ 0 hδ0.le hδ1 h3z h4z with hM₀
  have hp3 : ∀ a : Fin m, ∀ b : Fin m, 0 ≤ δ + (if b = a then ε else 0) := by
    intro a b
    by_cases h : b = a
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  have hp4 : ∀ a : Fin m, ∀ b : Fin m, δ + (if b = a then ε else 0) ≤ 1 := by
    intro a b
    by_cases h : b = a
    · rw [if_pos h]; linarith
    · rw [if_neg h]; linarith
  set Ma : Fin m → FiniteMDP 2 m := fun a =>
    G m δ (fun b => if b = a then ε else 0) hδ0.le hδ1 (hp3 a) (hp4 a) with hMa
  have hMa_r0 : ∀ a b, (Ma a).r 0 b = 0 := fun a b => G_r0 b
  have hMa_r1 : ∀ a b, (Ma a).r 1 b = 1 := fun a b => G_r1 b
  have hMa_P1 : ∀ a b, ((Ma a).P 1 b 0 : ℝ) = δ := fun a b => G_P1 b
  have hMa_P0 : ∀ a b, ((Ma a).P 0 b 1 : ℝ) = δ + (if b = a then ε else 0) :=
    fun a b => G_P0 b
  have hM₀_r0 : ∀ b, M₀.r 0 b = 0 := fun b => G_r0 b
  have hM₀_r1 : ∀ b, M₀.r 1 b = 1 := fun b => G_r1 b
  have hM₀_P1 : ∀ b, (M₀.P 1 b 0 : ℝ) = δ := fun b => G_P1 b
  have hM₀_P0 : ∀ b, (M₀.P 0 b 1 : ℝ) = δ := by
    intro b; simpa using (G_P0 (h1 := hδ0.le) (h2 := hδ1) (h3 := h3z) (h4 := h4z) b)
  -- the reference occupancy bounds, equation (35)
  obtain ⟨hC1, hC2⟩ :=
    BanditAlgorithm.jao_two_state_reference_occupancy_bounds δ hδ0 hδ M₀
      hM₀_r0 hM₀_r1 hM₀_P1 hM₀_P0 T π
  set V : Fin m → ℝ := fun b =>
    ∫ h, (mdpVisitCount h T 0 b : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac 0) π T) with hV
  set R : Fin m → ℝ := fun b =>
    ∫ h, mdpRegret (Ma b) T h ∂(mdpMeasure (Ma b) (mdpStateDirac 0) π T) with hR
  have hV0 : ∀ b, 0 ≤ V b := by
    intro b
    exact integral_nonneg fun h => by positivity
  -- the per-planting regret bound
  have hRbound : ∀ b : Fin m,
      (T : ℝ) * ((δ + ε) / (2 * δ + ε)) - (T : ℝ) + ((T : ℝ) / 2 - 1 / (2 * δ))
        - (ε / δ) * (V b + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V b))
        ≤ R b := by
    intro b
    have hgain :=
      BanditAlgorithm.jao_two_state_gadget_optimal_gain_ge δ ε hδ0 hδ hε0 hεδ b (Ma b)
        (hMa_r0 b) (hMa_r1 b) (hMa_P1 b) (hMa_P0 b)
    have heq34 :=
      BanditAlgorithm.jao_two_state_gadget_reward_le_reference_plus_planted_plays
        δ ε hδ0 hδ hε0 hεδ b (Ma b) M₀ (hMa_r0 b) (hMa_r1 b) (hMa_P1 b) (hMa_P0 b)
        hM₀_r0 hM₀_r1 hM₀_P1 hM₀_P0 T π
    have hlem13 :=
      BanditAlgorithm.jao_two_state_planted_plays_change_of_measure
        δ ε hδ0 hδ hε0 hεδ b (Ma b) M₀ (hMa_r0 b) (hMa_r1 b) (hMa_P1 b) (hMa_P0 b)
        hM₀_r0 hM₀_r1 hM₀_P1 hM₀_P0 T π
    have hsplit : R b = (T : ℝ) * mdpOptimalGain (Ma b)
        - ∫ h, mdpTrajectoryReward (Ma b) h ∂(mdpMeasure (Ma b) (mdpStateDirac 0) π T) := by
      simp only [hR, mdpRegret]
      rw [integral_sub Integrable.of_finite Integrable.of_finite]
      simp
    have hεδ' : 0 ≤ ε / δ := by positivity
    have hstep : (ε / δ)
        * ∫ h, (mdpVisitCount h T 0 b : ℝ) ∂(mdpMeasure (Ma b) (mdpStateDirac 0) π T)
        ≤ (ε / δ) * (V b + (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * V b)) :=
      mul_le_mul_of_nonneg_left hlem13 hεδ'
    have hgain' : (T : ℝ) * ((δ + ε) / (2 * δ + ε)) ≤ (T : ℝ) * mdpOptimalGain (Ma b) :=
      mul_le_mul_of_nonneg_left hgain hT0.le
    rw [hsplit]
    linarith
  obtain ⟨b, hb⟩ :=
    BanditAlgorithm.jao_collapsed_bandit_regret_arithmetic m hm δ ε hδ0 hδ T hT hεdef
      V R hV0 hC2 hRbound
  exact ⟨b, ε, Ma b, hε0, hεδ, hMa_r0 b, hMa_r1 b, hMa_P1 b, hMa_P0 b, hb⟩
