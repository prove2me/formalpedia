-- Prove2me | solution 1 for lean_workbook_plus_44908
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:04:26.009166+00:00
-- url     : https://prove2.me/submissions/feea1f36-d9c1-483e-ae05-4bf6631423f5

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace ReciprocalProductClassification

def Equation (a : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    f x * f y + f (a / x) * f (a / y) = 2 * f (x * y)

theorem nonnegative (a : ℝ) (f : ℝ → ℝ) (h : Equation a f)
    (x : ℝ) (hx : 0 < x) : 0 ≤ f x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have he := h (Real.sqrt x) (Real.sqrt x) hs hs
  rw [hs2] at he
  nlinarith [sq_nonneg (f (Real.sqrt x)), sq_nonneg (f (a / Real.sqrt x))]

theorem zero_branch (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h : Equation a f) (hfa : f a = 0) : ∀ x : ℝ, 0 < x → f x = 0 := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs2 : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hdiv : a / Real.sqrt a = Real.sqrt a := (div_eq_iff (ne_of_gt hs)).2 hs2.symm
  have he := h (Real.sqrt a) (Real.sqrt a) hs hs
  rw [hs2, hdiv, hfa] at he
  have hz : f (Real.sqrt a) = 0 := by nlinarith [sq_nonneg (f (Real.sqrt a))]
  have hi := h (Real.sqrt a) (1 / Real.sqrt a) hs (by positivity)
  have hprod : Real.sqrt a * (1 / Real.sqrt a) = 1 := by field_simp
  rw [hprod, hdiv, hz] at hi
  have h1 : f 1 = 0 := by nlinarith
  intro x hx
  have hp := h 1 x (by norm_num) hx
  simp only [div_one, one_mul, h1, hfa, zero_mul, zero_add] at hp
  linarith

theorem normalized_values (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h : Equation a f) (hfa : f a ≠ 0) : f 1 = 1 ∧ f a = 1 := by
  have he := h a 1 ha (by norm_num)
  simp only [div_self (ne_of_gt ha), div_one, mul_one] at he
  have hp : f a * (f 1 - 1) = 0 := by nlinarith
  have h1 : f 1 = 1 := by
    have hz := (mul_eq_zero.mp hp).resolve_left hfa
    linarith
  have hh := h 1 1 (by norm_num) (by norm_num)
  simp only [div_one, one_mul, h1] at hh
  exact ⟨h1, by nlinarith [nonnegative a f h a ha]⟩

theorem reflection (a : ℝ) (f : ℝ → ℝ) (h : Equation a f)
    (h1 : f 1 = 1) (hfa : f a = 1) (x : ℝ) (hx : 0 < x) : f (a / x) = f x := by
  have he := h 1 x (by norm_num) hx
  simp only [div_one, one_mul, h1, hfa] at he
  linarith

theorem multiplicative (a : ℝ) (f : ℝ → ℝ) (h : Equation a f)
    (h1 : f 1 = 1) (hfa : f a = 1) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    f (x * y) = f x * f y := by
  have he := h x y hx hy
  rw [reflection a f h h1 hfa x hx, reflection a f h h1 hfa y hy] at he
  linarith

theorem one_branch (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h : Equation a f) (hfa : f a ≠ 0) : ∀ x : ℝ, 0 < x → f x = 1 := by
  rcases normalized_values a ha f h hfa with ⟨h1, hA⟩
  intro x hx
  have he := multiplicative a f h h1 hA x (a / x) hx (div_pos ha hx)
  have hxdiv : x * (a / x) = a := by field_simp
  rw [hxdiv, hA, reflection a f h h1 hA x hx] at he
  nlinarith [nonnegative a f h x hx]

theorem classification (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) :
    Equation a f ↔ (∀ x : ℝ, 0 < x → f x = 0) ∨ (∀ x : ℝ, 0 < x → f x = 1) := by
  constructor
  · intro h
    by_cases hz : f a = 0
    · exact Or.inl (zero_branch a ha f h hz)
    · exact Or.inr (one_branch a ha f h hz)
  · rintro (h | h) x y hx hy
    · simp only [h x hx, h y hy, h (a / x) (div_pos ha hx),
        h (a / y) (div_pos ha hy), h (x * y) (mul_pos hx hy)]
      norm_num
    · simp only [h x hx, h y hy, h (a / x) (div_pos ha hx),
        h (a / y) (div_pos ha hy), h (x * y) (mul_pos hx hy)]
      norm_num

theorem source_classification (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ) :
    Equation a f ∧ f a = 1 ↔ ∀ x : ℝ, 0 < x → f x = 1 := by
  constructor
  · rintro ⟨he, hA⟩
    exact one_branch a ha f he (by rw [hA]; norm_num)
  · intro h
    exact ⟨(classification a ha f).2 (Or.inr h), h a ha⟩

theorem extension_classification (a : ℝ) (ha : 0 < a) (c : ℝ) (g : ℝ → ℝ) :
    Equation a (fun x => if 0 < x then c else g x) ↔ c = 0 ∨ c = 1 := by
  rw [classification a ha]
  constructor
  · rintro (h | h)
    · exact Or.inl (by simpa using h 1 (by norm_num))
    · exact Or.inr (by simpa using h 1 (by norm_num))
  · rintro (rfl | rfl)
    · exact Or.inl (by intro x hx; simp [hx])
    · exact Or.inr (by intro x hx; simp [hx])

theorem source_exists (a : ℝ) (ha : 0 < a) :
    ∃ f : ℝ → ℝ, Equation a f ∧ f a = 1 := by
  refine ⟨fun _ => 1, (source_classification a ha _).2 ?_⟩
  intro x hx
  rfl

end ReciprocalProductClassification

theorem solution (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (hf : ∀ x y : ℝ, (x * y > 0 ∧ f x * f y + f (a / x) * f (a / y) = 2 * f (x * y))) :
    ∃ c : ℝ, ∀ x : ℝ, (x > 0 → f x = c) := by
  have he : ReciprocalProductClassification.Equation a f := by
    intro x y hx hy
    exact (hf x y).2
  rcases (ReciprocalProductClassification.classification a ha f).1 he with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
