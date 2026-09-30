-- Prove2me | solution 1 for lean_workbook_plus_10219
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:27:27.017291+00:00
-- url     : https://prove2.me/submissions/510c9435-5eb4-4359-87e3-e7b9ce2bd616

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace QuarticMonotonicityAndRange

def value (x : ℝ) : ℝ := x ^ 4 - 4 * x + 1

theorem continuous_value : Continuous value := by
  unfold value
  fun_prop

theorem hasDerivAt_value (x : ℝ) : HasDerivAt value (4 * x ^ 3 - 4) x := by
  convert (((hasDerivAt_id x).pow 4).sub
    ((hasDerivAt_id x).const_mul 4)).add_const 1 using 1
  norm_num [value]

theorem decreasing : StrictAntiOn value (Set.Iic 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic 1) continuous_value.continuousOn
  intro x hx
  rw [interior_Iic] at hx
  have h : x ^ 3 < (1 : ℝ) ^ 3 := (show Odd 3 by decide).strictMono_pow hx
  rw [(hasDerivAt_value x).deriv]
  norm_num at h
  linarith

theorem increasing : StrictMonoOn value (Set.Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) continuous_value.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have h : (1 : ℝ) ^ 3 < x ^ 3 := (show Odd 3 by decide).strictMono_pow hx
  rw [(hasDerivAt_value x).deriv]
  norm_num at h
  linarith

theorem minimum_bound (x : ℝ) : -2 ≤ value x := by
  dsimp [value]
  nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]

theorem minimum_eq_iff (x : ℝ) : value x = -2 ↔ x = 1 := by
  constructor
  · intro hx
    have h : (x - 1) ^ 2 = 0 := by
      dsimp [value] at hx
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
    have := sq_eq_zero_iff.mp h
    linarith
  · rintro rfl
    norm_num [value]

theorem quadratic_lower_bound (x : ℝ) : (x - 1) ^ 2 - 2 ≤ value x := by
  dsimp [value]
  nlinarith [sq_nonneg (x - 1),
    mul_nonneg (sq_nonneg (x - 1)) (sq_nonneg (x + 1))]

theorem exists_left (y : ℝ) (hy : -2 ≤ y) : ∃ x ≤ 1, value x = y := by
  have hb : value (-(y + 4)) ≥ y := by
    have := quadratic_lower_bound (-(y + 4))
    nlinarith [sq_nonneg (y + 2)]
  have h1 : value 1 ≤ y := by norm_num [value]; exact hy
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc'
    (show -(y + 4) ≤ (1 : ℝ) by linarith) continuous_value.continuousOn ⟨h1, hb⟩
  exact ⟨x, hx.2, hxy⟩

theorem exists_right (y : ℝ) (hy : -2 ≤ y) : ∃ x ≥ 1, value x = y := by
  have hb : value (y + 4) ≥ y := by
    have := quadratic_lower_bound (y + 4)
    nlinarith [sq_nonneg (y + 2)]
  have h1 : value 1 ≤ y := by norm_num [value]; exact hy
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc
    (show (1 : ℝ) ≤ y + 4 by linarith) continuous_value.continuousOn ⟨h1, hb⟩
  exact ⟨x, hx.1, hxy⟩

theorem left_range : value '' Set.Iic 1 = Set.Ici (-2) := by
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    exact minimum_bound x
  · intro hy
    obtain ⟨x, hx, hxy⟩ := exists_left y hy
    exact ⟨x, hx, hxy⟩

theorem right_range : value '' Set.Ici 1 = Set.Ici (-2) := by
  ext y
  constructor
  · rintro ⟨x, _, rfl⟩
    exact minimum_bound x
  · intro hy
    obtain ⟨x, hx, hxy⟩ := exists_right y hy
    exact ⟨x, hx, hxy⟩

theorem full_range : Set.range value = Set.Ici (-2) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact minimum_bound x
  · intro hy
    obtain ⟨x, _, hxy⟩ := exists_right y hy
    exact ⟨x, hxy⟩

theorem no_preimage (y : ℝ) (hy : y < -2) : ¬ ∃ x, value x = y := by
  rintro ⟨x, rfl⟩
  exact (not_lt_of_ge (minimum_bound x)) hy

theorem two_preimages (y : ℝ) (hy : -2 < y) :
    ∃ u v, u < 1 ∧ 1 < v ∧
      ∀ x, value x = y ↔ x = u ∨ x = v := by
  obtain ⟨u, hu, huy⟩ := exists_left y hy.le
  obtain ⟨v, hv, hvy⟩ := exists_right y hy.le
  have hu' : u < 1 := lt_of_le_of_ne hu (by
    intro heq
    subst u
    norm_num [value] at huy
    linarith)
  have hv' : 1 < v := lt_of_le_of_ne hv (by
    intro heq
    subst v
    norm_num [value] at hvy
    linarith)
  refine ⟨u, v, hu', hv', fun x => ⟨?_, ?_⟩⟩
  · intro hxy
    rcases le_total x 1 with hx | hx
    · exact Or.inl (decreasing.injOn hx hu (hxy.trans huy.symm))
    · exact Or.inr (increasing.injOn hx hv (hxy.trans hvy.symm))
  · rintro (rfl | rfl)
    · exact huy
    · exact hvy

theorem source_injective : Set.InjOn value (Set.Icc 0 1) :=
  decreasing.injOn.mono (fun _ hx => hx.2)

theorem source_range : value '' Set.Icc 0 1 = Set.Icc (-2) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨minimum_bound x, ?_⟩
    have := decreasing.antitoneOn (show (0 : ℝ) ∈ Set.Iic 1 by norm_num) hx.2 hx.1
    simpa [value] using this
  · intro hy
    apply intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
      continuous_value.continuousOn
    norm_num [value]
    exact hy

end QuarticMonotonicityAndRange

theorem solution (f : ℝ → ℝ) (hf : f = fun x => x ^ 4 - 4 * x + 1) :
    ∀ x ∈ [0, 1], ∀ y ∈ [0, 1], f x = f y → x = y := by
  subst f
  intro x hx y hy hxy
  apply QuarticMonotonicityAndRange.source_injective
  · rcases List.mem_cons.mp hx with rfl | hx
    · norm_num
    · simp only [List.mem_singleton] at hx
      subst x
      norm_num
  · rcases List.mem_cons.mp hy with rfl | hy
    · norm_num
    · simp only [List.mem_singleton] at hy
      subst y
      norm_num
  · exact hxy

#print axioms QuarticMonotonicityAndRange.value
#print axioms QuarticMonotonicityAndRange.continuous_value
#print axioms QuarticMonotonicityAndRange.hasDerivAt_value
#print axioms QuarticMonotonicityAndRange.decreasing
#print axioms QuarticMonotonicityAndRange.increasing
#print axioms QuarticMonotonicityAndRange.minimum_bound
#print axioms QuarticMonotonicityAndRange.minimum_eq_iff
#print axioms QuarticMonotonicityAndRange.quadratic_lower_bound
#print axioms QuarticMonotonicityAndRange.exists_left
#print axioms QuarticMonotonicityAndRange.exists_right
#print axioms QuarticMonotonicityAndRange.left_range
#print axioms QuarticMonotonicityAndRange.right_range
#print axioms QuarticMonotonicityAndRange.full_range
#print axioms QuarticMonotonicityAndRange.no_preimage
#print axioms QuarticMonotonicityAndRange.two_preimages
#print axioms QuarticMonotonicityAndRange.source_injective
#print axioms QuarticMonotonicityAndRange.source_range
#print axioms solution
