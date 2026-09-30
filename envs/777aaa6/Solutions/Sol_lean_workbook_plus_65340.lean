-- Prove2me | solution 1 for lean_workbook_plus_65340
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:00:34.530557+00:00
-- url     : https://prove2.me/submissions/fbe38959-c080-4991-ba51-125d65fe297a

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace WeightedReflection

theorem classification {K : Type*} [Field K] [NeZero (2 : K)] (f : K → K) :
    (∀ x, f x + (1 - x) * f (-x) = x ^ 2) ↔ f = id := by
  constructor
  · intro hf
    funext x
    by_cases hx : x = 0
    · subst x
      have hz := hf 0
      simp only [neg_zero, sub_zero, one_mul, zero_pow (by decide : 2 ≠ 0)] at hz
      have ht : (2 : K) * f 0 = 0 := by linear_combination hz
      exact (mul_eq_zero.mp ht).resolve_left (NeZero.ne (2 : K))
    · have hp := hf x
      have hm := hf (-x)
      simp only [neg_neg, sub_neg_eq_add, neg_sq] at hm
      have hdet : x ^ 2 * (f x - x) = 0 := by
        linear_combination hp - (1 - x) * hm
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left (pow_ne_zero 2 hx))
  · rintro rfl x
    simp only [id_eq]
    ring

theorem source_unique : ∃! f : ℝ → ℝ,
    ∀ x, f x + (1 - x) * f (-x) = x ^ 2 := by
  refine ⟨id, (classification id).mpr rfl, ?_⟩
  exact fun f hf => (classification f).mp hf

end WeightedReflection

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x, f x + (1 - x) * f (-x) = x ^ 2) :
    ∀ x, f (-x) + (1 + x) * f x = x ^ 2 := by
  have h := (WeightedReflection.classification f).mp hf
  subst f
  intro x
  simp only [id_eq]
  ring
