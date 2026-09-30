-- Prove2me | solution 1 for lean_workbook_plus_9183
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:50:28.495922+00:00
-- url     : https://prove2.me/submissions/1a445983-a5b3-4c24-901e-45bdaa42361f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace DilationTranslationCompatibility

def Equation (a b c d h : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x, f (2 * x) = a * f x + b) ∧
    ∀ x, f (x + h) = c * f x + d

theorem constant_iff (a b c d h k : ℝ) :
    Equation a b c d h (fun _ => k) ↔
      (1 - a) * k = b ∧ (1 - c) * k = d := by
  constructor
  · rintro ⟨hD, hT⟩
    constructor <;> nlinarith [hD 0, hT 0]
  · rintro ⟨ha, hc⟩
    constructor <;> intro x <;> dsimp <;> nlinarith

theorem zero_dilation (b c d h : ℝ) (f : ℝ → ℝ)
    (hf : Equation 0 b c d h f) : ∀ x, f x = b := by
  intro x
  simpa only [show (2 : ℝ) * (x / 2) = x by ring, zero_mul, zero_add]
    using hf.1 (x / 2)

theorem zero_translation (a b d h : ℝ) (f : ℝ → ℝ)
    (hf : Equation a b 0 d h f) : ∀ x, f x = d := by
  intro x
  simpa only [sub_add_cancel, zero_mul, zero_add] using hf.2 (x - h)

theorem two_path_identity (a b c d h : ℝ) (f : ℝ → ℝ)
    (hf : Equation a b c d h f) (x : ℝ) :
    a * c * (c - 1) * f x = (a - c - 1) * d + (1 - c ^ 2) * b := by
  have he : a * (c * f x + d) + b = c * (c * (a * f x + b) + d) + d := by
    calc
      a * (c * f x + d) + b = f (2 * (x + h)) := by rw [hf.1, hf.2]
      _ = f ((2 * x + h) + h) := by congr 1; ring
      _ = c * (c * (a * f x + b) + d) + d := by rw [hf.2, hf.2, hf.1]
  linear_combination -he

theorem constant_of_translation_ne_one (a b c d h : ℝ) (f : ℝ → ℝ)
    (hc : c ≠ 1) (hf : Equation a b c d h f) : ∀ x, f x = f 0 := by
  by_cases ha : a = 0
  · subst a
    intro x
    rw [zero_dilation b c d h f hf x, zero_dilation b c d h f hf 0]
  by_cases hc0 : c = 0
  · subst c
    intro x
    rw [zero_translation a b d h f hf x, zero_translation a b d h f hf 0]
  intro x
  have hn : a * c * (c - 1) ≠ 0 := mul_ne_zero (mul_ne_zero ha hc0) (sub_ne_zero.mpr hc)
  apply mul_left_cancel₀ hn
  rw [two_path_identity a b c d h f hf x, two_path_identity a b c d h f hf 0]

theorem coefficient_compatibility (a b c d h : ℝ) (f : ℝ → ℝ)
    (hc : c ≠ 1) (hf : Equation a b c d h f) :
    (1 - c) * b = (1 - a) * d := by
  have hD := hf.1 0
  have hT := hf.2 0
  simp only [mul_zero, zero_add] at hD hT
  rw [constant_of_translation_ne_one a b c d h f hc hf h] at hT
  linear_combination (1 - a) * hT - (1 - c) * hD

theorem forced_value (a b c d h : ℝ) (f : ℝ → ℝ)
    (hc : c ≠ 1) (hf : Equation a b c d h f) (x : ℝ) : f x = d / (1 - c) := by
  have hv := constant_of_translation_ne_one a b c d h f hc hf
  have ht := hf.2 0
  simp only [zero_add] at ht
  rw [hv h] at ht
  rw [hv x]
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hc))).2
  nlinarith

theorem constant_model (a b c d h : ℝ) (hc : c ≠ 1)
    (hab : (1 - c) * b = (1 - a) * d) :
    Equation a b c d h (fun _ => d / (1 - c)) := by
  apply (constant_iff a b c d h _).2
  have hn : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  constructor
  · apply mul_right_cancel₀ hn
    calc
      ((1 - a) * (d / (1 - c))) * (1 - c) = (1 - a) * d := by field_simp
      _ = b * (1 - c) := by nlinarith [hab]
  · field_simp

theorem full_classification (a b c d h : ℝ) (f : ℝ → ℝ) (hc : c ≠ 1) :
    Equation a b c d h f ↔
      (1 - c) * b = (1 - a) * d ∧ f = fun _ => d / (1 - c) := by
  constructor
  · intro hf
    exact ⟨coefficient_compatibility a b c d h f hc hf,
      funext (forced_value a b c d h f hc hf)⟩
  · rintro ⟨hab, rfl⟩
    exact constant_model a b c d h hc hab

theorem existence_iff (a b c d h : ℝ) (hc : c ≠ 1) :
    (∃ f, Equation a b c d h f) ↔ (1 - c) * b = (1 - a) * d := by
  constructor
  · rintro ⟨f, hf⟩
    exact coefficient_compatibility a b c d h f hc hf
  · intro hab
    exact ⟨_, constant_model a b c d h hc hab⟩

theorem unique_existence_iff (a b c d h : ℝ) (hc : c ≠ 1) :
    (∃! f, Equation a b c d h f) ↔ (1 - c) * b = (1 - a) * d := by
  constructor
  · rintro ⟨f, hf, _⟩
    exact coefficient_compatibility a b c d h f hc hf
  · intro hab
    refine ⟨fun _ => d / (1 - c), constant_model a b c d h hc hab, ?_⟩
    intro f hf
    exact (full_classification a b c d h f hc).1 hf |>.2

theorem multiplier_one_necessary (a b d h : ℝ) (f : ℝ → ℝ)
    (hf : Equation a b 1 d h f) : (a - 2) * d = 0 := by
  have he := two_path_identity a b 1 d h f hf 0
  nlinarith [he]

theorem multiplier_one_nonconstant (h : ℝ) :
    Equation 2 0 1 h h id ∧ ¬ ∃ k : ℝ, ∀ x : ℝ, id x = k := by
  constructor
  · constructor <;> intro x <;> simp [id_eq]
  · rintro ⟨k, hk⟩
    have h0 := hk 0
    have h1 := hk 1
    norm_num at h0 h1
    linarith

theorem source_inconsistent (f : ℝ → ℝ) (h1 : f 1 = 1)
    (hD : ∀ x, f (2 * x) = 4 * f x + 6)
    (hT : ∀ x, f (x + 4) = 4 * f x + 4 * f 1 + 8 * f 2) : False := by
  have h2 : f 2 = 10 := by
    have he := hD 1
    norm_num [h1] at he
    exact he
  have hf : Equation 4 6 4 84 4 f := by
    refine ⟨hD, ?_⟩
    intro x
    have he := hT x
    rw [h1, h2] at he
    nlinarith [he]
  have he := coefficient_compatibility 4 6 4 84 4 f (by norm_num) hf
  norm_num at he

theorem source_solution_set_empty :
    {f : ℝ → ℝ | f 1 = 1 ∧ (∀ x, f (2 * x) = 4 * f x + 6) ∧
      ∀ x, f (x + 4) = 4 * f x + 4 * f 1 + 8 * f 2} = ∅ := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h1, hD, hT⟩
  exact source_inconsistent f h1 hD hT

end DilationTranslationCompatibility

theorem solution (f : ℝ → ℝ) (hf1 : f 1 = 1)
    (hf2 : ∀ x, f (2 * x) = 4 * f x + 6)
    (hf3 : ∀ x, f (x + 4) = 4 * f x + 4 * f 1 + 8 * f 2) : f 6 = 106 := by
  exact (DilationTranslationCompatibility.source_inconsistent f hf1 hf2 hf3).elim
