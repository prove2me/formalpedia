-- Prove2me | solution 1 for BanditAlgorithm.mdp_regret_lower_bound_jao_per_initial_state_large_diameter
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T03:07:23.528772+00:00
-- url     : https://prove2.me/submissions/725d5a76-464c-458e-ad9f-8c9fb68a70a8

import Theorems.Thm_BanditAlgorithm_jao_planted_two_class_mdp_regret_core_per_initial_state
import Theorems.Thm_BanditAlgorithm_jao_composite_two_class_gadget_construction

open MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
        20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
          ∀ π : MDPPolicy S A, ∀ s : Fin S,
            ∃ M : FiniteMDP S A,
              mdpDiameterENN M ≤ ENNReal.ofReal D ∧
              C * Real.sqrt (D * S * A * T) ≤
                ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  obtain ⟨c, hc, hcore⟩ := BanditAlgorithm.jao_planted_two_class_mdp_regret_core_per_initial_state
  refine ⟨c * (5 / 22), by positivity, ?_⟩
  intro S A T D hS hA hD hT hD12 π s
  set m : ℕ := S / 2 * (A / 2) with hm
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hD12
  set δ : ℝ := 4 / D with hδ
  have hδ0 : 0 < δ := div_pos (by norm_num) hD0
  have hδ3 : δ ≤ 1 / 3 := by rw [hδ, div_le_iff₀ hD0]; linarith
  -- `m = ⌊S/2⌋·⌊A/2⌋ ≥ 25`
  have hm20 : 20 ≤ m := by
    have h1 : 5 ≤ S / 2 := by omega
    have h2 : 5 ≤ A / 2 := by omega
    calc (20 : ℕ) ≤ 5 * 5 := by norm_num
      _ ≤ (S / 2) * (A / 2) := Nat.mul_le_mul h1 h2
  -- `4m ≤ SA`: the composite MDP fits in `S` states and `A` actions
  have hmSA : 4 * m ≤ S * A := by
    have h1 : 2 * (S / 2) ≤ S := by omega
    have h2 : 2 * (A / 2) ≤ A := by omega
    calc 4 * m = (2 * (S / 2)) * (2 * (A / 2)) := by rw [hm]; ring
      _ ≤ S * A := Nat.mul_le_mul h1 h2
  -- `25·SA ≤ 121·m`: the conversion constant, tight at `(S,A) = (11,11)`
  have hratio : 25 * (S * A) ≤ 121 * m := by
    have h1 : 10 * S ≤ 11 * (2 * (S / 2)) := by omega
    have h2 : 10 * A ≤ 11 * (2 * (A / 2)) := by omega
    have h4 : 4 * (25 * (S * A)) ≤ 4 * (121 * m) := by
      calc 4 * (25 * (S * A)) = (10 * S) * (10 * A) := by ring
        _ ≤ (11 * (2 * (S / 2))) * (11 * (2 * (A / 2))) := Nat.mul_le_mul h1 h2
        _ = 4 * (121 * m) := by rw [hm]; ring
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  -- the core's horizon hypothesis `16m ≤ δT` is exactly `4mD ≤ T`, from `T ≥ DSA`
  have hT16 : (16 : ℝ) * m ≤ δ * T := by
    have hcast : (4 * m : ℝ) ≤ (S : ℝ) * A := by exact_mod_cast hmSA
    have h4mD : 4 * (m : ℝ) * D ≤ (T : ℝ) := by
      linarith [mul_le_mul_of_nonneg_right hcast hD0.le]
    rw [hδ, div_mul_eq_mul_div, le_div_iff₀ hD0]
    linarith
  have hm0 : (0 : ℝ) < m := by
    have : (20 : ℝ) ≤ m := by exact_mod_cast hm20
    linarith
  have hT0 : (0 : ℝ) < T := by nlinarith
  -- the planted boost `ε = (1/5)√(δm/T)` satisfies `20ε ≤ δ`
  set ε : ℝ := 1 / 5 * Real.sqrt (δ * m / T) with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hεδ : 20 * ε ≤ 4 / D := by
    have hsq : δ * m / T ≤ (δ / 4) ^ 2 := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity)] at this
    rw [hεdef, ← hδ]
    linarith
  obtain ⟨ρ, up, down, nav, arm, M, M₀, hinj, harm0, hself, hupdown, hρ01,
      hr₀, hrow0₀, hrow1₀, hrM, hrow0, hrow1, hdiam⟩ :=
    BanditAlgorithm.jao_composite_two_class_gadget_construction S A hS hA D hD12 hD ε hε0 hεδ
  obtain ⟨i, hbound⟩ :=
    hcore S A m hm20 δ hδ0 hδ3 T hT16 ε rfl ρ up down nav arm M M₀ hinj harm0 hself hupdown
      hρ01 hr₀ hrow0₀ hrow1₀ hrM hrow0 hrow1 π s
  refine ⟨M i, hdiam i, le_trans ?_ hbound⟩
  -- `(5c/22)·√(DSAT) ≤ c·√(Tm/δ)`, i.e. `25·SA ≤ 121·m` after squaring
  have hTm : (0 : ℝ) ≤ (T : ℝ) * m / δ := by positivity
  have key : (5 / 22 : ℝ) ^ 2 * (D * S * A * T) ≤ (T : ℝ) * m / δ := by
    have hr : (25 : ℝ) * ((S : ℝ) * A) ≤ 121 * m := by exact_mod_cast hratio
    rw [hδ, div_div_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith [mul_le_mul_of_nonneg_right hr (mul_nonneg hT0.le hD0.le)]
  have hsplit : Real.sqrt ((5 / 22 : ℝ) ^ 2 * (D * S * A * T))
      = (5 / 22 : ℝ) * Real.sqrt (D * S * A * T) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (5 / 22 : ℝ) ^ 2),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5 / 22)]
  calc c * (5 / 22) * Real.sqrt (D * S * A * T)
      = c * Real.sqrt ((5 / 22 : ℝ) ^ 2 * (D * S * A * T)) := by rw [hsplit]; ring
    _ ≤ c * Real.sqrt ((T : ℝ) * m / δ) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt key) hc.le
