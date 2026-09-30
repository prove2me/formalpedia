-- Prove2me | solution 1 for lean_workbook_plus_42314
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:41:26.861+00:00
-- url     : https://prove2.me/submissions/1b80b403-5248-4d7a-96f8-e36d935cc821

import Mathlib

set_option autoImplicit false

namespace QuarticMiddleDoubleRoot

def value (x : ℝ) : ℝ := x ^ 4 - 14 * x ^ 3 + 64 * x ^ 2 - 114 * x + 63

def rootData : Multiset ℝ := {1, 3, 3, 7}

noncomputable def polynomial : Polynomial ℝ :=
  (rootData.map fun a => Polynomial.X - Polynomial.C a).prod

theorem factorization (x : ℝ) :
    value x = (x - 3) ^ 2 * ((x - 1) * (x - 7)) := by
  unfold value
  ring

theorem polynomial_eval (x : ℝ) : polynomial.eval x = value x := by
  simp [polynomial, rootData]
  unfold value
  ring

theorem root_multiset : polynomial.roots = rootData :=
  Polynomial.roots_multiset_prod_X_sub_C rootData

theorem multiplicity (x : ℝ) :
    Polynomial.rootMultiplicity x polynomial =
      if x = 3 then 2 else if x = 1 ∨ x = 7 then 1 else 0 := by
  classical
  rw [← Polynomial.count_roots, root_multiset]
  by_cases h3 : x = 3
  · subst x
    norm_num [rootData]
  by_cases h1 : x = 1
  · subst x
    norm_num [rootData]
  by_cases h7 : x = 7
  · subst x
    norm_num [rootData]
  simp [rootData, h3, h1, h7]

theorem roots_iff (x : ℝ) : value x = 0 ↔ x = 1 ∨ x = 3 ∨ x = 7 := by
  rw [factorization]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), sub_eq_zero]
  tauto

theorem root_set : {x : ℝ | value x = 0} = {1, 3, 7} := by
  ext x
  simpa only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using roots_iff x

theorem distinct_root_count : Set.ncard {x : ℝ | value x = 0} = 3 := by
  classical
  rw [root_set]
  have hs : ({1, 3, 7} : Set ℝ) = ↑({1, 3, 7} : Finset ℝ) := by ext x; simp
  rw [hs, Set.ncard_coe_finset]
  norm_num

theorem negative_iff (x : ℝ) : value x < 0 ↔ 1 < x ∧ x < 7 ∧ x ≠ 3 := by
  rw [factorization]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨hs, hp⟩ | ⟨hs, _⟩
    · have h3 : x ≠ 3 := by intro hx; subst x; norm_num at hs
      rcases mul_neg_iff.mp hp with ⟨h1, h7⟩ | ⟨h1, h7⟩
      · exact ⟨by linarith, by linarith, h3⟩
      · linarith
    · exact False.elim ((sq_nonneg (x - 3)).not_gt hs)
  · rintro ⟨h1, h7, h3⟩
    have hs : 0 < (x - 3) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr h3)
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg (by linarith) (by linarith))

theorem nonnegative_iff (x : ℝ) : 0 ≤ value x ↔ x ≤ 1 ∨ x = 3 ∨ 7 ≤ x := by
  rw [← not_lt, negative_iff]
  push_neg
  constructor
  · intro h
    by_cases h1 : x ≤ 1
    · exact Or.inl h1
    by_cases h7 : 7 ≤ x
    · exact Or.inr (Or.inr h7)
    exact Or.inr (Or.inl (h (lt_of_not_ge h1) (lt_of_not_ge h7)))
  · rintro (h1 | h3 | h7) hx1 hx7
    · linarith
    · exact h3
    · linarith

theorem nonpositive_iff (x : ℝ) : value x ≤ 0 ↔ 1 ≤ x ∧ x ≤ 7 := by
  constructor
  · intro h
    rcases eq_or_lt_of_le h with he | hn
    · rcases (roots_iff x).mp he with rfl | rfl | rfl <;> norm_num
    · obtain ⟨h1, h7, _⟩ := (negative_iff x).mp hn
      exact ⟨h1.le, h7.le⟩
  · rintro ⟨h1, h7⟩
    rw [factorization]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) <|
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h1) (sub_nonpos.mpr h7)

theorem positive_iff (x : ℝ) : 0 < value x ↔ x < 1 ∨ 7 < x := by
  rw [← not_le, nonpositive_iff]
  push_neg
  constructor
  · intro h
    by_cases hx : x < 1
    · exact Or.inl hx
    exact Or.inr (h (le_of_not_gt hx))
  · rintro (hx | hx) h1
    · linarith
    · exact hx

theorem root_endpoints :
    IsLeast {x : ℝ | value x = 0} 1 ∧ IsGreatest {x : ℝ | value x = 0} 7 := by
  constructor
  · refine ⟨(roots_iff 1).mpr (Or.inl rfl), ?_⟩
    intro x hx
    rcases (roots_iff x).mp hx with rfl | rfl | rfl <;> norm_num
  · refine ⟨(roots_iff 7).mpr (Or.inr (Or.inr rfl)), ?_⟩
    intro x hx
    rcases (roots_iff x).mp hx with rfl | rfl | rfl <;> norm_num

theorem source_bounds (x : ℝ) (hx : value x = 0) : 0 < x ∧ x < 14 := by
  rcases (roots_iff x).mp hx with rfl | rfl | rfl <;> norm_num

end QuarticMiddleDoubleRoot

theorem solution (x : ℝ) :
    x ^ 4 - 14 * x ^ 3 + 64 * x ^ 2 - 114 * x + 63 = 0 → 0 < x ∧ x < 14 := by
  exact QuarticMiddleDoubleRoot.source_bounds x
