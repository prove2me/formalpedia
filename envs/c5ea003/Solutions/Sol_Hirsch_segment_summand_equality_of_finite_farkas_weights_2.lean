-- Prove2me | solution 2 for Hirsch.segment_summand_equality_of_finite_farkas_weights
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T19:09:46.516051+00:00
-- url     : https://prove2.me/submissions/f55f421b-7e4c-4bea-8bdb-8c9ed1429b61

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

private lemma segment_scalar_bound (α t τ : ℝ) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    t * α ≤ τ * max α 0 := by
  by_cases hα : 0 ≤ α
  · rw [max_eq_left hα]
    exact mul_le_mul_of_nonneg_right htτ hα
  · have hα' : α ≤ 0 := le_of_not_ge hα
    rw [max_eq_right hα']
    nlinarith

private lemma split_parameter_bounds (τ U : ℝ) (hτ : 0 ≤ τ) (hU : 0 ≤ U) :
    0 ≤ max 0 (τ-U) ∧ max 0 (τ-U) ≤ τ ∧ τ-max 0 (τ-U) ≤ U := by
  refine ⟨le_max_left _ _, max_le hτ (by linarith), ?_⟩
  have h := le_max_right 0 (τ-U)
  linarith

private theorem exists_upper_fiber_end
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E)
    (hx : ∀ i, a i x ≤ b i) (hplus : ∃ i, 0 < a i g) :
    ∃ i : ι, 0 < a i g ∧
      0 ≤ (b i-a i x)/(a i g) ∧
      ∀ j, 0 < a j g →
        ((b i-a i x)/(a i g))*(a j g) ≤ b j-a j x := by
  classical
  let S := Finset.univ.filter (fun i : ι => 0 < a i g)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hplus
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image S (fun j => (b j-a j x)/(a j g)) hS
  have hip : 0 < a i g := (Finset.mem_filter.mp hi).2
  refine ⟨i, hip, div_nonneg (sub_nonneg.mpr (hx i)) hip.le, ?_⟩
  intro j hj
  have h := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  exact (le_div_iff₀ hj).mp h

private theorem pair_width_of_farkas
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (cert : ∀ i j, 0 < a i g → a j g < 0 →
      ∃ w : ι → ℝ,
        (∀ k, 0 ≤ w k) ∧
        (∑ k, w k • a k) = (-a j g) • a i + (a i g) • a j ∧
        (∑ k, w k * b k) ≤
          (-a j g) * b i + (a i g) * b j - τ * (a i g) * (-a j g))
    (x : E) (hx : ∀ k, a k x ≤ b k) (i j : ι)
    (hi : 0 < a i g) (hj : a j g < 0) :
    τ*(a i g)*(-a j g) ≤ (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) := by
  obtain ⟨w, hw, hnormal, hconst⟩ := cert i j hi hj
  have hs : (∑ k, w k * a k x) ≤ ∑ k, w k * b k := by
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hx k) (hw k))
  have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hnormal
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
  nlinarith

theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g : E) (τ : ℝ)
    (hτ : 0 ≤ τ) (hplus : ∃ i, 0 < a i g)
    (cert : ∀ i j, 0 < a i g → a j g < 0 →
      ∃ w : ι → ℝ,
        (∀ k, 0 ≤ w k) ∧
        (∑ k, w k • a k) = (-a j g) • a i + (a i g) • a j ∧
        (∑ k, w k * b k) ≤
          (-a j g) * b i + (a i g) * b j - τ * (a i g) * (-a j g)) :
    {x : E | ∀ i, a i x ≤ b i} =
      {x : E | ∃ p : E,
        (∀ i, a i p ≤ b i - τ * max (a i g) 0) ∧
        ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g} := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hip, hU, hupper⟩ := exists_upper_fiber_end a b g x hx hplus
    let U := (b i-a i x)/(a i g)
    let t := max 0 (τ-U)
    have hU0 : 0 ≤ U := hU
    obtain ⟨ht0, htτ, htU⟩ := split_parameter_bounds τ U hτ hU0
    have hUi : U*(a i g)=b i-a i x := div_mul_cancel₀ _ (ne_of_gt hip)
    refine ⟨x-t • g, ?_, t, ht0, htτ, ?_⟩
    · intro j
      have hjx := hx j
      simp only [map_sub, map_smul, smul_eq_mul]
      by_cases hjpos : 0 < a j g
      · rw [max_eq_left hjpos.le]
        have hbound := hupper j hjpos
        have hmul := mul_le_mul_of_nonneg_right htU hjpos.le
        dsimp [t,U] at *
        nlinarith
      · have hjnon : a j g ≤ 0 := le_of_not_gt hjpos
        rw [max_eq_right hjnon]
        by_cases hjzero : a j g = 0
        · simp [hjzero]
          exact hjx
        · have hjneg : a j g < 0 := lt_of_le_of_ne hjnon hjzero
          have pair := pair_width_of_farkas a b g τ cert x hx i j hip hjneg
          have pair' : τ*(a i g)*(-a j g) ≤
              (-a j g)*(U*(a i g))+(a i g)*(b j-a j x) := by
            rw [hUi]
            exact pair
          have hbound : (τ-U)*(-a j g) ≤ b j-a j x := by
            nlinarith [pair']
          by_cases hdiff : τ-U ≤ 0
          · have ht : t = 0 := max_eq_left hdiff
            simp only [ht, zero_mul, mul_zero, sub_zero]
            exact hjx
          · have ht : t = τ-U := max_eq_right (le_of_not_ge hdiff)
            rw [ht]
            nlinarith
    · module
  · rintro x ⟨p, hp, t, ht, htτ, rfl⟩ i
    have h := hp i
    have hs := segment_scalar_bound (a i g) t τ ht htτ
    simp only [map_add,map_smul,smul_eq_mul]
    linarith

#print axioms solution
