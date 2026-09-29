-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_easy_sqrt_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:09:58.408185+00:00
-- url     : https://prove2.me/submissions/8ab001f2-d821-449d-896b-1f33c27a4e31

import Theorems.Thm_BanditAlgorithm_partial_monitoring_easy_geometric_alternatives_of_outside
import Theorems.Thm_BanditAlgorithm_partial_monitoring_sqrt_lower_of_geometric_alternatives
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_transverse_direction
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_positive_common_point
import Theorems.Thm_BanditAlgorithm_partial_monitoring_neighbour_loss_interpolation
import Theorems.Thm_stdSimplex_small_perturbation
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set

namespace BanditAlgorithm

private theorem full_neighbourhood_geometric_alternatives
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (hab : NeighbouringActions G a b)
    (hall : ∀ c : Fin k, c ∈ pmNeighbourhood G a b) :
    ∃ a b : Fin k, ∃ u q : Fin d → ℝ, ∃ ε δ : ℝ,
      NeighbouringActions G a b ∧ 0 < ε ∧ 0 < δ ∧
      (∑ i, q i) = 0 ∧
      (∑ i, (G.L a i - G.L b i) * q i) = 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ δ →
        let ua := fun i ↦ u i - Δ * q i
        let ub := fun i ↦ u i + Δ * q i
        ua ∈ pmCell G a ∧ ub ∈ pmCell G b ∧
        (∀ c : Fin k, c ∉ pmNeighbourhood G a b →
          ε / 2 ≤ ∑ i, (G.L c i - G.L a i) * ua i ∧
          ε / 2 ≤ ∑ i, (G.L c i - G.L b i) * ub i) ∧
        (∀ c : Fin k, c ∈ pmNeighbourhood G a b →
          (∑ i, (G.L c i - G.L a i) * ua i) +
          (∑ i, (G.L c i - G.L b i) * ub i) = Δ) := by
  classical
  obtain ⟨q, hqsum, hqnorm⟩ :=
    partial_monitoring_neighbour_transverse_direction G a b hab
  obtain ⟨u, hu, hupos⟩ :=
    partial_monitoring_neighbour_positive_common_point G a b hab
  obtain ⟨δ, hδ, hsimp⟩ := stdSimplex_small_perturbation u q hu.1.1 hupos hqsum
  refine ⟨a, b, u, q, δ, δ, hab, hδ, hδ, hqsum, hqnorm, ?_⟩
  intro Δ hΔ hΔδ
  dsimp only
  have hΔabs : |Δ| = Δ := abs_of_pos hΔ
  have hDs : |Δ| ≤ δ := by simpa [hΔabs] using hΔδ
  have huaS : (fun i ↦ u i - Δ * q i) ∈ stdSimplex ℝ (Fin d) := by
    convert hsimp (-Δ) (by simpa [abs_neg] using hDs) using 1
    ext i
    ring
  have hubS : (fun i ↦ u i + Δ * q i) ∈ stdSimplex ℝ (Fin d) := hsimp Δ hDs
  have huv : ∑ i, (G.L a i - G.L b i) * u i = 0 := by
    have habu := hu.1.2 b
    have hbau := hu.2.2 a
    have hneg : (∑ i, (G.L b i - G.L a i) * u i) =
        -(∑ i, (G.L a i - G.L b i) * u i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg] at hbau
    linarith
  have hbu : ∑ i, (G.L b i - G.L a i) * u i = 0 := by
    have hneg : (∑ i, (G.L b i - G.L a i) * u i) =
        -(∑ i, (G.L a i - G.L b i) * u i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, huv, neg_zero]
  have hbq : ∑ i, (G.L b i - G.L a i) * q i = -1 := by
    have hneg : (∑ i, (G.L b i - G.L a i) * q i) =
        -(∑ i, (G.L a i - G.L b i) * q i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, hqnorm]
  have hinsideA : ∀ c : Fin k,
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        (∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) = (1 - α) * Δ := by
    intro c
    obtain ⟨α, hα0, hα1, hα⟩ :=
      partial_monitoring_neighbour_loss_interpolation G a b hab c (hall c)
    refine ⟨α, hα0, hα1, ?_⟩
    calc
      (∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) =
          ∑ i, ((1 - α) * (G.L b i - G.L a i)) * (u i - Δ * q i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hα i]
            ring
      _ = (1 - α) * ∑ i, (G.L b i - G.L a i) * (u i - Δ * q i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (1 - α) * ((∑ i, (G.L b i - G.L a i) * u i) -
            Δ * ∑ i, (G.L b i - G.L a i) * q i) := by
            congr 1
            calc
              _ = ∑ i, ((G.L b i - G.L a i) * u i -
                  Δ * ((G.L b i - G.L a i) * q i)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (1 - α) * Δ := by rw [hbu, hbq]; ring
  have hinsideB : ∀ c : Fin k,
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧
        (∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) = α * Δ := by
    intro c
    obtain ⟨α, hα0, hα1, hα⟩ :=
      partial_monitoring_neighbour_loss_interpolation G a b hab c (hall c)
    refine ⟨α, hα0, hα1, ?_⟩
    calc
      (∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) =
          ∑ i, (α * (G.L a i - G.L b i)) * (u i + Δ * q i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hα i]
            ring
      _ = α * ∑ i, (G.L a i - G.L b i) * (u i + Δ * q i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = α * ((∑ i, (G.L a i - G.L b i) * u i) +
            Δ * ∑ i, (G.L a i - G.L b i) * q i) := by
            congr 1
            calc
              _ = ∑ i, ((G.L a i - G.L b i) * u i +
                  Δ * ((G.L a i - G.L b i) * q i)) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    ring
              _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = α * Δ := by rw [huv, hqnorm]; ring
  have hua : (fun i ↦ u i - Δ * q i) ∈ pmCell G a := by
    refine ⟨huaS, ?_⟩
    intro c
    obtain ⟨α, hα0, hα1, hca⟩ := hinsideA c
    have hnonneg : 0 ≤ ∑ i, (G.L c i - G.L a i) * (u i - Δ * q i) := by
      rw [hca]
      exact mul_nonneg (sub_nonneg.mpr hα1) hΔ.le
    have hneg : (∑ i, (G.L a i - G.L c i) * (u i - Δ * q i)) =
        -(∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    linarith
  have hub : (fun i ↦ u i + Δ * q i) ∈ pmCell G b := by
    refine ⟨hubS, ?_⟩
    intro c
    obtain ⟨α, hα0, hα1, hcb⟩ := hinsideB c
    have hnonneg : 0 ≤ ∑ i, (G.L c i - G.L b i) * (u i + Δ * q i) := by
      rw [hcb]
      exact mul_nonneg hα0 hΔ.le
    have hneg : (∑ i, (G.L b i - G.L c i) * (u i + Δ * q i)) =
        -(∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg]
    linarith
  refine ⟨hua, hub, ?_, ?_⟩
  · intro c hc
    exact (hc (hall c)).elim
  · intro c hc
    obtain ⟨γ, -, -, hγ⟩ :=
      partial_monitoring_neighbour_loss_interpolation G a b hab c hc
    calc
      (∑ i, (G.L c i - G.L a i) * (u i - Δ * q i)) +
          (∑ i, (G.L c i - G.L b i) * (u i + Δ * q i)) =
        ∑ i, (((2 * γ - 1) * (G.L a i - G.L b i)) * u i +
          Δ * ((G.L a i - G.L b i) * q i)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [hγ i]
            ring
      _ = (2 * γ - 1) * (∑ i, (G.L a i - G.L b i) * u i) +
          Δ * (∑ i, (G.L a i - G.L b i) * q i) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
      _ = Δ := by rw [huv, hqnorm]; ring

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : LocallyObservable G ∧ HasNeighbouringActions G) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * Real.sqrt n ≤ pmMinimaxRegret G n := by
  classical
  obtain ⟨a, b, hab⟩ := h.2
  by_cases hout : ∃ c : Fin k, c ∉ pmNeighbourhood G a b
  · have hgeom := partial_monitoring_easy_geometric_alternatives_of_outside
      G a b hab hout
    exact partial_monitoring_sqrt_lower_of_geometric_alternatives G hgeom
  · have hall : ∀ c : Fin k, c ∈ pmNeighbourhood G a b := by
      push Not at hout
      exact hout
    have hgeom := full_neighbourhood_geometric_alternatives G a b hab hall
    exact partial_monitoring_sqrt_lower_of_geometric_alternatives G hgeom

