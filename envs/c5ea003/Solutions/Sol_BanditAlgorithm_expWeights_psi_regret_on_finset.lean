-- Prove2me | solution 1 for BanditAlgorithm.expWeights_psi_regret_on_finset
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:28:18.666795+00:00
-- url     : https://prove2.me/submissions/b024d656-ae2f-4c0d-b561-af8d422825a5

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Order

open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution
    {k : ℕ} (S : Finset (Fin k)) (hS : S.Nonempty)
    (n : ℕ) (η : ℝ) (hη : 0 < η) (y : ℕ → Fin k → ℝ) :
    let W := fun t : ℕ ↦
      ∑ a ∈ S, Real.exp (- (η * ∑ s ∈ Finset.range t, y s a))
    let Q := fun t : ℕ ↦ fun a : Fin k ↦
      if a ∈ S then Real.exp (- (η * ∑ s ∈ Finset.range t, y s a)) / W t else 0
    ∀ a₀ ∈ S,
      (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * (y t a - y t a₀)) ≤
        Real.log S.card / η + (1 / η) *
          ∑ t ∈ Finset.range n, ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by
  dsimp only
  intro a₀ ha₀
  let W := fun t : ℕ ↦
    ∑ a ∈ S, Real.exp (- (η * ∑ s ∈ Finset.range t, y s a))
  let Q := fun t : ℕ ↦ fun a : Fin k ↦
    if a ∈ S then Real.exp (- (η * ∑ s ∈ Finset.range t, y s a)) / W t else 0
  have hWpos (t : ℕ) : 0 < W t := by
    dsimp [W]
    exact Finset.sum_pos (fun a ha ↦ Real.exp_pos _) hS
  have hWzero : W 0 = S.card := by
    simp [W]
  have hQsum (t : ℕ) : ∑ a : Fin k, Q t a = 1 := by
    dsimp [Q]
    rw [Finset.sum_ite]
    simp only [Finset.filter_univ_mem, Finset.sum_const_zero, add_zero,
      div_eq_mul_inv]
    rw [← Finset.sum_mul]
    change W t * (W t)⁻¹ = 1
    exact mul_inv_cancel₀ (hWpos t).ne'
  have hWstep (t : ℕ) :
      W (t + 1) / W t = ∑ a : Fin k, Q t a * Real.exp (-η * y t a) := by
    dsimp [Q]
    simp only [ite_mul, zero_mul, Finset.sum_ite, Finset.filter_univ_mem,
      Finset.sum_const_zero, add_zero]
    rw [div_eq_iff (hWpos t).ne']
    rw [Finset.sum_mul]
    dsimp [W]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_range_succ]
    rw [show -(η * (∑ s ∈ Finset.range t, y s a + y t a)) =
        (- (η * ∑ s ∈ Finset.range t, y s a)) + (-η * y t a) by ring,
      Real.exp_add]
    field_simp
    symm
    apply div_self
    simpa [W] using (hWpos t).ne'
  have hlogstep (t : ℕ) :
      Real.log (W (t + 1)) - Real.log (W t) ≤
        ∑ a : Fin k, Q t a * (Real.exp (-η * y t a) - 1) := by
    rw [← Real.log_div (hWpos (t + 1)).ne' (hWpos t).ne']
    calc
      Real.log (W (t + 1) / W t) ≤ W (t + 1) / W t - 1 :=
        Real.log_le_sub_one_of_pos (div_pos (hWpos (t + 1)) (hWpos t))
      _ = ∑ a : Fin k, Q t a * (Real.exp (-η * y t a) - 1) := by
        rw [hWstep]
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hQsum]
  have hstep (t : ℕ) :
      (∑ a : Fin k, Q t a * y t a) ≤
        (Real.log (W t) - Real.log (W (t + 1))) / η +
          (1 / η) * ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by
    have hpsi :
        (∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1)) =
          (∑ a : Fin k, Q t a * (Real.exp (-η * y t a) - 1)) +
            η * ∑ a : Fin k, Q t a * y t a := by
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, mul_one]
      have hscale :
          (∑ x : Fin k, Q t x * (η * y t x)) =
            η * ∑ x : Fin k, Q t x * y t x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hscale]
      ring
    rw [hpsi]
    rw [div_eq_mul_inv, one_div]
    have hηinv : 0 < η⁻¹ := inv_pos.mpr hη
    have hnonneg : 0 ≤
        (Real.log (W t) - Real.log (W (t + 1))) +
          ∑ a : Fin k, Q t a * (Real.exp (-η * y t a) - 1) := by
      linarith [hlogstep t]
    calc
      (∑ a : Fin k, Q t a * y t a) ≤
          (∑ a : Fin k, Q t a * y t a) + η⁻¹ *
            ((Real.log (W t) - Real.log (W (t + 1))) +
              ∑ a : Fin k, Q t a * (Real.exp (-η * y t a) - 1)) :=
        le_add_of_nonneg_right (mul_nonneg hηinv.le hnonneg)
      _ = (Real.log (W t) - Real.log (W (t + 1))) * η⁻¹ +
          η⁻¹ * ((∑ a : Fin k, Q t a * (Real.exp (-η * y t a) - 1)) +
            η * ∑ a : Fin k, Q t a * y t a) := by
        field_simp
        ring
  have hsumstep :
      (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * y t a) ≤
        (Real.log (W 0) - Real.log (W n)) / η +
          (1 / η) * ∑ t ∈ Finset.range n, ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by
    calc
      (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * y t a) ≤
          ∑ t ∈ Finset.range n,
            ((Real.log (W t) - Real.log (W (t + 1))) / η +
              (1 / η) * ∑ a : Fin k,
                Q t a * (Real.exp (-η * y t a) + η * y t a - 1)) :=
        Finset.sum_le_sum fun t ht ↦ hstep t
      _ = (Real.log (W 0) - Real.log (W n)) / η +
          (1 / η) * ∑ t ∈ Finset.range n, ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by
        rw [Finset.sum_add_distrib]
        simp only [div_eq_mul_inv, one_div]
        rw [← Finset.sum_mul, Finset.sum_range_sub']
        rw [Finset.mul_sum]
  have htermle :
      Real.exp (- (η * ∑ s ∈ Finset.range n, y s a₀)) ≤ W n := by
    dsimp [W]
    exact Finset.single_le_sum
      (f := fun a : Fin k ↦ Real.exp (- (η * ∑ s ∈ Finset.range n, y s a)))
      (fun a ha ↦ (Real.exp_pos _).le) ha₀
  have hloglower :
      -(η * ∑ s ∈ Finset.range n, y s a₀) ≤ Real.log (W n) := by
    have := Real.log_le_log (Real.exp_pos _) htermle
    simpa using this
  have hmain :
      (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * y t a) -
          ∑ t ∈ Finset.range n, y t a₀ ≤
        Real.log S.card / η + (1 / η) *
          ∑ t ∈ Finset.range n, ∑ a : Fin k,
            Q t a * (Real.exp (-η * y t a) + η * y t a - 1) := by
    rw [hWzero] at hsumstep
    rw [div_eq_mul_inv, one_div] at hsumstep ⊢
    have hηinv : 0 ≤ η⁻¹ := (inv_pos.mpr hη).le
    have hscaled := mul_le_mul_of_nonneg_left hloglower hηinv
    have hscaled' :
        -(∑ s ∈ Finset.range n, y s a₀) ≤ η⁻¹ * Real.log (W n) := by
      calc
        -(∑ s ∈ Finset.range n, y s a₀) =
            η⁻¹ * (-(η * ∑ s ∈ Finset.range n, y s a₀)) := by
          field_simp
        _ ≤ η⁻¹ * Real.log (W n) := hscaled
    linarith
  calc
    (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * (y t a - y t a₀)) =
        (∑ t ∈ Finset.range n, ∑ a : Fin k, Q t a * y t a) -
          ∑ t ∈ Finset.range n, y t a₀ := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      apply congrArg₂ (fun x z : ℝ ↦ x - z) rfl
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_mul]
      rw [hQsum]
      simp
    _ ≤ _ := hmain

end BanditAlgorithm
