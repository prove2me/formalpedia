-- Prove2me | solution 3 for BanditAlgorithm.linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T19:55:00.119897+00:00
-- url     : https://prove2.me/submissions/0cf504a5-4a9e-4c1f-a868-14b9c0c53e4f

import Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_hypercube_average_reward_upper_bound
import Mathlib.Tactic

open MeasureTheory
open Matrix

namespace BanditAlgorithm

private def bayesSign {d : ℕ} (σ : Fin d → Bool) (i : Fin d) : ℝ :=
  if σ i then 1 else -1

private theorem bayesSign_sq {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    bayesSign σ i ^ 2 = 1 := by
  simp [bayesSign]

private noncomputable def bayesDelta (d n : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) / (48 * n))

private noncomputable def bayesTheta {d : ℕ} (n : ℕ)
    (σ : Fin d → Bool) : Fin d → ℝ :=
  fun i ↦ bayesDelta d n * bayesSign σ i

private theorem dot_bayesSign_le_sqrt {d : ℕ} (hd : 0 < d)
    (a : Fin d → ℝ) (ha : a ⬝ᵥ a ≤ 1) (σ : Fin d → Bool) :
    a ⬝ᵥ bayesSign σ ≤ Real.sqrt d := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a (bayesSign σ)
  have hasa : (∑ i : Fin d, a i ^ 2) = a ⬝ᵥ a := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsig : (∑ i : Fin d, bayesSign σ i ^ 2) = d := by
    simp [bayesSign_sq]
  rw [hasa, hsig] at hcs
  have hsqrta : Real.sqrt (a ⬝ᵥ a) ≤ 1 := by
    calc
      Real.sqrt (a ⬝ᵥ a) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ha
      _ = 1 := by norm_num
  calc
    a ⬝ᵥ bayesSign σ = ∑ i, a i * bayesSign σ i := rfl
    _ ≤ Real.sqrt (a ⬝ᵥ a) * Real.sqrt d := hcs
    _ ≤ 1 * Real.sqrt d := by
      gcongr
    _ = Real.sqrt d := one_mul _

private theorem sSup_unitBall_bayesTheta {d n : ℕ} (hd : 0 < d)
    (σ : Fin d → Bool) :
    sSup ((fun a ↦ a ⬝ᵥ bayesTheta n σ) ''
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}) =
      bayesDelta d n * Real.sqrt d := by
  have hΔ : 0 ≤ bayesDelta d n := by
    dsimp [bayesDelta]
    positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  let u : Fin d → ℝ := fun i ↦ bayesSign σ i / Real.sqrt d
  have huA : u ⬝ᵥ u ≤ 1 := by
    have hsqrt_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
      Real.sq_sqrt hdR.le
    have hdot : u ⬝ᵥ u = 1 := by
      simp only [u, dotProduct]
      calc
        (∑ i, bayesSign σ i / Real.sqrt d *
            (bayesSign σ i / Real.sqrt d)) =
            ∑ _i : Fin d, (1 : ℝ) / d := by
              apply Finset.sum_congr rfl
              intro i hi
              have hs := bayesSign_sq σ i
              field_simp [ne_of_gt hsqrtd]
              nlinarith
        _ = 1 := by
          simp
          field_simp
    rw [hdot]
  have hudot : u ⬝ᵥ bayesTheta n σ =
      bayesDelta d n * Real.sqrt d := by
    have hsqrt_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
      Real.sq_sqrt hdR.le
    simp only [u, bayesTheta, dotProduct]
    calc
      (∑ i, bayesSign σ i / Real.sqrt d *
          (bayesDelta d n * bayesSign σ i)) =
          ∑ _i : Fin d, bayesDelta d n / Real.sqrt d := by
            apply Finset.sum_congr rfl
            intro i hi
            have hs := bayesSign_sq σ i
            field_simp [ne_of_gt hsqrtd]
            nlinarith
      _ = bayesDelta d n * Real.sqrt d := by
        simp
        field_simp [ne_of_gt hsqrtd]
        nlinarith
  have hmem :
      bayesDelta d n * Real.sqrt d ∈
        (fun a ↦ a ⬝ᵥ bayesTheta n σ) ''
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} :=
    ⟨u, huA, hudot⟩
  have hub : ∀ y ∈
      (fun a ↦ a ⬝ᵥ bayesTheta n σ) ''
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1},
      y ≤ bayesDelta d n * Real.sqrt d := by
    rintro y ⟨a, ha, rfl⟩
    have hdot := dot_bayesSign_le_sqrt hd a ha σ
    have heq : a ⬝ᵥ bayesTheta n σ =
        bayesDelta d n * (a ⬝ᵥ bayesSign σ) := by
      simp only [bayesTheta, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    change a ⬝ᵥ bayesTheta n σ ≤
      bayesDelta d n * Real.sqrt d
    rw [heq]
    exact mul_le_mul_of_nonneg_left hdot hΔ
  have hnonempty :
      ((fun a ↦ a ⬝ᵥ bayesTheta n σ) ''
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}).Nonempty :=
    ⟨_, hmem⟩
  have hbdd : BddAbove
      ((fun a ↦ a ⬝ᵥ bayesTheta n σ) ''
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}) :=
    ⟨_, hub⟩
  apply le_antisymm
  · exact csSup_le hnonempty hub
  · exact le_csSup hbdd hmem

end BanditAlgorithm

open BanditAlgorithm

theorem solution {d n : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    (Fintype.card (Fin d → Bool) : ℝ) *
          (n * Δ * Real.sqrt d / 4) ≤
      ∑ σ : Fin d → Bool,
        linearBanditExpectedRegret
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
          (fun i ↦ Δ * if σ i then 1 else -1) π n := by
  classical
  have hn : 0 < n := by omega
  let C : ℝ := Fintype.card (Fin d → Bool)
  let Δ : ℝ := bayesDelta d n
  let G : (Fin d → Bool) → ℝ := fun σ ↦
    ∫ h, ∑ t, (h t).1 ⬝ᵥ bayesTheta n σ
      ∂linearBanditMeasure (bayesTheta n σ) π n
  have hreward : (∑ σ : Fin d → Bool, G σ) ≤
      C * (n * Δ ^ 2 * Real.sqrt n) := by
    simpa only [C, Δ, G, bayesDelta, bayesTheta, bayesSign] using
      linear_bandit_unit_ball_hypercube_average_reward_upper_bound
        hd hn π hsupp
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, bayesDelta]
    positivity
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrtn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hΔsq : Δ ^ 2 = (d : ℝ) / (48 * n) := by
    dsimp [Δ, bayesDelta]
    exact Real.sq_sqrt (by positivity)
  have hsqrtn_sq : Real.sqrt (n : ℝ) ^ 2 = n :=
    Real.sq_sqrt (by positivity)
  have hsqrtd_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
    Real.sq_sqrt (by positivity)
  have hsmall : Δ * Real.sqrt n ≤ 3 * Real.sqrt d / 4 := by
    have hleft_nonneg : 0 ≤ Δ * Real.sqrt n := mul_nonneg hΔ hsqrtn
    have hright_nonneg : 0 ≤ 3 * Real.sqrt d / 4 := by positivity
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hleft_sq :
        (Δ * Real.sqrt n) ^ 2 = (d : ℝ) / 48 := by
      rw [mul_pow, hΔsq, hsqrtn_sq]
      field_simp [ne_of_gt hnR]
    have hright_sq :
        (3 * Real.sqrt d / 4) ^ 2 = 9 * (d : ℝ) / 16 := by
      rw [div_pow, mul_pow, hsqrtd_sq]
      norm_num
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith
  have hreward' :
      (∑ σ : Fin d → Bool, G σ) ≤
        C * (3 * (n * Δ * Real.sqrt d) / 4) := by
    calc
      (∑ σ : Fin d → Bool, G σ)
          ≤ C * (n * Δ ^ 2 * Real.sqrt n) := hreward
      _ ≤ C * (3 * (n * Δ * Real.sqrt d) / 4) := by
        have hC : 0 ≤ C := by dsimp [C]; positivity
        apply mul_le_mul_of_nonneg_left _ hC
        have hnR : 0 ≤ (n : ℝ) := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hsmall
          (mul_nonneg hnR hΔ)
        convert hscaled using 1 <;> ring
  change C * (n * Δ * Real.sqrt d / 4) ≤
    ∑ σ : Fin d → Bool,
      linearBanditExpectedRegret
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
        (bayesTheta n σ) π n
  have hsumReg :
      (∑ σ : Fin d → Bool,
        linearBanditExpectedRegret
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
          (bayesTheta n σ) π n) =
        C * (n * Δ * Real.sqrt d) - ∑ σ, G σ := by
    simp_rw [linearBanditExpectedRegret, sSup_unitBall_bayesTheta hd]
    dsimp [G, C, Δ]
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsumReg]
  linarith
