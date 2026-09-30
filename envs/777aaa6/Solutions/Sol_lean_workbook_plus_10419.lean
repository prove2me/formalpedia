-- Prove2me | solution 1 for lean_workbook_plus_10419
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:30:45.116728+00:00
-- url     : https://prove2.me/submissions/9acdc827-3040-4496-b51d-1e7acfad5500

import Mathlib

namespace RationalCircleTripleParametrization

def System (a b c : ℚ) : Prop := a + b + c = 1 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 1

def den (t : ℚ) : ℚ := t ^ 2 + t + 1

def point (t : ℚ) : ℚ × ℚ × ℚ :=
  (-t / den t, t * (t + 1) / den t, (t + 1) / den t)

theorem den_positive (t : ℚ) : 0 < den t := by
  unfold den
  nlinarith [sq_nonneg (2 * t + 1)]

theorem parameter_model (t : ℚ) : System (point t).1 (point t).2.1 (point t).2.2 := by
  constructor <;> dsimp [point] <;>
    field_simp [ne_of_gt (den_positive t)] <;> unfold den <;> ring

theorem coordinate_relation (t : ℚ) : (point t).2.1 = t * (point t).2.2 := by
  dsimp [point]
  ring

theorem zero_third_coordinate (t : ℚ) : (point t).2.2 = 0 ↔ t = -1 := by
  change (t + 1) / den t = 0 ↔ t = -1
  constructor
  · intro h
    have hz := (div_eq_iff (ne_of_gt (den_positive t))).mp h
    linarith
  · rintro rfl
    norm_num [den]

theorem parameter_injective : Function.Injective point := by
  intro t u he
  have hb : (point t).2.1 = (point u).2.1 :=
    congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) he
  have hc : (point t).2.2 = (point u).2.2 :=
    congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) he
  by_cases hct : (point t).2.2 = 0
  · have ht := (zero_third_coordinate t).mp hct
    have hu := (zero_third_coordinate u).mp (hc.symm.trans hct)
    exact ht.trans hu.symm
  · have hbt := coordinate_relation t
    have hbu := coordinate_relation u
    rw [← hc] at hbu
    have hz : (t - u) * (point t).2.2 = 0 := by nlinarith only [hb, hbt, hbu]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hct)

theorem full_classification (a b c : ℚ) : System a b c ↔
    (a = 0 ∧ b = 1 ∧ c = 0) ∨
    ∃ t : ℚ, a = (point t).1 ∧ b = (point t).2.1 ∧ c = (point t).2.2 := by
  constructor
  · intro h
    have hs : (a + b + c) ^ 2 = 1 := by rw [h.1]; ring
    have hp : a * b + b * c + c * a = 0 := by nlinarith only [h.2, hs]
    by_cases hc : c = 0
    · simp only [hc, mul_zero, zero_mul, add_zero] at hp
      rcases mul_eq_zero.mp hp with ha | hb
      · exact Or.inl ⟨ha, by linarith [h.1], hc⟩
      · have ha : a = 1 := by linarith [h.1]
        refine Or.inr ⟨-1, ?_, ?_, ?_⟩
        · simpa [point, den] using ha
        · simpa [point, den] using hb
        · simpa [point, den] using hc
    · let t := b / c
      have hb : b = t * c := by dsimp [t]; field_simp [hc]
      have ha : a = 1 - (t + 1) * c := by linarith only [h.1, hb]
      rw [ha, hb] at hp
      have hz : c * (den t * c - (t + 1)) = 0 := by
        unfold den
        linear_combination -hp
      have hr := (mul_eq_zero.mp hz).resolve_left hc
      have hcc : c = (t + 1) / den t := by
        apply (eq_div_iff (ne_of_gt (den_positive t))).mpr
        nlinarith only [hr]
      refine Or.inr ⟨t, ?_, ?_, hcc⟩
      · change a = -t / den t
        rw [ha, hcc]
        field_simp [ne_of_gt (den_positive t)]
        unfold den
        ring
      · change b = t * (t + 1) / den t
        rw [hb, hcc]
        ring
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨t, ha, hb, hc⟩)
    · constructor <;> ring
    · rw [ha, hb, hc]
      exact parameter_model t

theorem exceptional_point_not_parameterized (t : ℚ) : point t ≠ (0, 1, 0) := by
  intro he
  have hc : (point t).2.2 = 0 := congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) he
  have hb : (point t).2.1 = 1 := congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) he
  have hr := coordinate_relation t
  rw [hc, hb, mul_zero] at hr
  norm_num at hr

theorem infinitely_many_solutions :
    Set.Infinite {p : ℚ × ℚ × ℚ | System p.1 p.2.1 p.2.2} := by
  apply (Set.infinite_range_of_injective parameter_injective).mono
  rintro p ⟨t, rfl⟩
  exact parameter_model t

end RationalCircleTripleParametrization

theorem solution (a b c : ℚ) (ha : a + b + c = 1) (hb : a ^ 2 + b ^ 2 + c ^ 2 = 1) :
    ∃ a b c : ℚ, a + b + c = 1 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 1 := ⟨a, b, c, ha, hb⟩

#print axioms RationalCircleTripleParametrization.den_positive
#print axioms RationalCircleTripleParametrization.parameter_model
#print axioms RationalCircleTripleParametrization.coordinate_relation
#print axioms RationalCircleTripleParametrization.zero_third_coordinate
#print axioms RationalCircleTripleParametrization.parameter_injective
#print axioms RationalCircleTripleParametrization.full_classification
#print axioms RationalCircleTripleParametrization.exceptional_point_not_parameterized
#print axioms RationalCircleTripleParametrization.infinitely_many_solutions
#print axioms solution
