-- Prove2me | solution 1 for MarkovMixing.metropolized_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:51:42.779875+00:00
-- url     : https://prove2.me/submissions/10d6f22a-b3f8-4c90-9b8e-1ff144691f3f

import Definitions.Def_mm_mcmc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (hΨ : IsStochastic Ψ)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x) :
    IsStochastic (metropolized Ψ π) ∧
    DetailedBalance (metropolized Ψ π) π ∧
    IsStationary (metropolized Ψ π) π := by
  classical
  have hminmul : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * min 1 (b / a) = min a b := by
    intro a b ha hb
    rcases eq_or_lt_of_le ha with h | ha'
    · rw [← h, zero_mul, min_eq_left hb]
    · rcases le_total b a with h | h
      · rw [min_eq_right (by rw [div_le_one ha']; exact h), min_eq_right h]
        field_simp
      · rw [min_eq_left (by rw [le_div_iff₀ ha']; linarith), min_eq_left h, mul_one]
  have hoff : ∀ x y : V, y ≠ x →
      metropolized Ψ π x y = Ψ x y * min 1 (π y * Ψ y x / (π x * Ψ x y)) := by
    intro x y hxy
    show (if y = x then _ else _) = _
    rw [if_neg hxy]
  have hdiag : ∀ x : V, metropolized Ψ π x x
      = 1 - ∑ z ∈ ({x}ᶜ : Finset V), Ψ x z * min 1 (π z * Ψ z x / (π x * Ψ x z)) := by
    intro x
    show (if x = x then _ else _) = _
    rw [if_pos rfl]
  have hacc_nonneg : ∀ x y : V, 0 ≤ min 1 (π y * Ψ y x / (π x * Ψ x y)) :=
    fun x y => le_min zero_le_one
      (div_nonneg (mul_nonneg (hpos y).le (hΨ.1 y x)) (mul_nonneg (hpos x).le (hΨ.1 x y)))
  have hacc_le : ∀ x y : V, min 1 (π y * Ψ y x / (π x * Ψ x y)) ≤ 1 :=
    fun x y => min_le_left _ _
  have hrow : ∀ x : V, ∑ y, metropolized Ψ π x y = 1 := by
    intro x
    have hsp : ∑ y ∈ ({x}ᶜ : Finset V), metropolized Ψ π x y
        + ∑ y ∈ ({x} : Finset V), metropolized Ψ π x y = ∑ y, metropolized Ψ π x y :=
      Finset.sum_compl_add_sum _ _
    rw [← hsp, Finset.sum_singleton, hdiag x]
    have hcongr : ∑ y ∈ ({x}ᶜ : Finset V), metropolized Ψ π x y
        = ∑ y ∈ ({x}ᶜ : Finset V), Ψ x y * min 1 (π y * Ψ y x / (π x * Ψ x y)) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [hoff x y (by simpa using Finset.mem_compl.mp hy)]
    rw [hcongr]
    ring
  have hnonneg : ∀ x y : V, 0 ≤ metropolized Ψ π x y := by
    intro x y
    by_cases hxy : y = x
    · subst hxy
      rw [hdiag y]
      have hle : ∑ z ∈ ({y}ᶜ : Finset V), Ψ y z * min 1 (π z * Ψ z y / (π y * Ψ y z))
          ≤ ∑ z ∈ ({y}ᶜ : Finset V), Ψ y z := by
        refine Finset.sum_le_sum fun z _ => ?_
        calc Ψ y z * min 1 (π z * Ψ z y / (π y * Ψ y z)) ≤ Ψ y z * 1 :=
              mul_le_mul_of_nonneg_left (hacc_le y z) (hΨ.1 y z)
          _ = Ψ y z := mul_one _
      have hsum : ∑ z ∈ ({y}ᶜ : Finset V), Ψ y z + Ψ y y = 1 := by
        have h := Finset.sum_compl_add_sum ({y} : Finset V) (fun z => Ψ y z)
        rw [Finset.sum_singleton] at h
        rw [h]
        exact hΨ.2 y
      have := hΨ.1 y y
      linarith
    · rw [hoff x y hxy]
      exact mul_nonneg (hΨ.1 x y) (hacc_nonneg x y)
  have hstoch : IsStochastic (metropolized Ψ π) := ⟨hnonneg, hrow⟩
  have hdb : DetailedBalance (metropolized Ψ π) π := by
    intro x y
    by_cases hxy : y = x
    · subst hxy; rfl
    · have hyx : x ≠ y := fun h => hxy h.symm
      rw [hoff x y hxy, hoff y x hyx]
      have hA : (0:ℝ) ≤ π x * Ψ x y := mul_nonneg (hpos x).le (hΨ.1 x y)
      have hB : (0:ℝ) ≤ π y * Ψ y x := mul_nonneg (hpos y).le (hΨ.1 y x)
      have h1 : π x * (Ψ x y * min 1 (π y * Ψ y x / (π x * Ψ x y)))
          = min (π x * Ψ x y) (π y * Ψ y x) := by
        rw [← hminmul _ _ hA hB]; ring
      have h2 : π y * (Ψ y x * min 1 (π x * Ψ x y / (π y * Ψ y x)))
          = min (π y * Ψ y x) (π x * Ψ x y) := by
        rw [← hminmul _ _ hB hA]; ring
      rw [h1, h2, min_comm]
  refine ⟨hstoch, hdb, hπ, ?_⟩
  funext y
  show ∑ x, π x * metropolized Ψ π x y = π y
  rw [Finset.sum_congr rfl fun x _ => (hdb y x).symm, ← Finset.mul_sum, hrow y, mul_one]
