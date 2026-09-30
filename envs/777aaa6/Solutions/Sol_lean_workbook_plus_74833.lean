-- Prove2me | solution 1 for lean_workbook_plus_74833
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:21:13.54394+00:00
-- url     : https://prove2.me/submissions/35b6bd81-7836-4809-83e7-9e787a449777

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

def compositionFixedPointEquiv {α β : Type*} (f : α → β) (g : β → α) :
    {x : α // g (f x) = x} ≃ {y : β // f (g y) = y} where
  toFun x := ⟨f x, congrArg f x.property⟩
  invFun y := ⟨g y, congrArg g y.property⟩
  left_inv x := Subtype.ext x.property
  right_inv y := Subtype.ext y.property

theorem square_cube_composition_compatibility (f g : ℝ → ℝ)
    (hf : ∀ x, f (g x) = x ^ 2) (hg : ∀ x, g (f x) = x ^ 3) :
    ∀ x, f (x ^ 3) = f x ^ 2 ∧ g (x ^ 2) = g x ^ 3 := by
  intro x
  constructor
  · rw [← hg x, hf (f x)]
  · rw [← hf x, hg (g x)]

theorem square_cube_compositions_impossible :
    ¬ ∃ f g : ℝ → ℝ, (∀ x, f (g x) = x ^ 2) ∧ (∀ x, g (f x) = x ^ 3) := by
  rintro ⟨f, g, hf, hg⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have hcube : x ^ 3 = y ^ 3 := by simpa only [hg] using congrArg g hxy
    exact (Odd.pow_inj (by decide : Odd 3)).mp hcube
  have hfixed (t : ℝ) (ht : t ^ 3 = t) : f t = 0 ∨ f t = 1 := by
    have he := (square_cube_composition_compatibility f g hf hg t).1
    rw [ht] at he
    have hp : f t * (f t - 1) = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).imp id (fun h => sub_eq_zero.mp h)
  have hm := hfixed (-1) (by norm_num)
  have h0 := hfixed 0 (by norm_num)
  have h1 := hfixed 1 (by norm_num)
  have hcollision : f (-1) = f 0 ∨ f (-1) = f 1 ∨ f 0 = f 1 := by
    rcases hm with hm | hm <;> rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    all_goals first
      | exact Or.inl (hm.trans h0.symm)
      | exact Or.inr (Or.inl (hm.trans h1.symm))
      | exact Or.inr (Or.inr (h0.trans h1.symm))
  rcases hcollision with he | he | he
  · have hc := hinj he
    norm_num at hc
  · have hc := hinj he
    norm_num at hc
  · have hc := hinj he
    norm_num at hc

theorem solution (f g : ℝ → ℝ) (hf : ∀ x, f (g x) = x ^ 2)
    (hg : ∀ x, g (f x) = x ^ 3) :
    ∀ x, f (x ^ 3) = f x ^ 2 ∧ g (x ^ 2) = g x ^ 3 :=
  square_cube_composition_compatibility f g hf hg

#print axioms solution
#print axioms compositionFixedPointEquiv
#print axioms square_cube_composition_compatibility
#print axioms square_cube_compositions_impossible
