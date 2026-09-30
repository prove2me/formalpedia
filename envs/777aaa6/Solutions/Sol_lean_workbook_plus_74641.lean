-- Prove2me | solution 1 for lean_workbook_plus_74641
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:01:54.821748+00:00
-- url     : https://prove2.me/submissions/51f27137-c34e-4eea-9fcf-ecc997e468d6

import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem weighted_jensen_affine (α β : ℝ) (h : α + β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (f : ℝ → ℝ) (hf : Continuous f)
    (hfe : ∀ x y : ℝ, f (α * x + β * y) = α * f x + β * f y) :
    ∀ x : ℝ, f x = (f 1 - f 0) * x + f 0 := by
  have hc : α * f 0 + β * f 0 = f 0 := by
    rw [← add_mul, h, one_mul]
  have hadd (u v : ℝ) : f (u + v) - f 0 = (f u - f 0) + (f v - f 0) := by
    have hu : α * (u / α) = u := by field_simp
    have hv : β * (v / β) = v := by field_simp
    have hfu := hfe (u / α) 0
    have hfv := hfe 0 (v / β)
    have hfuv := hfe (u / α) (v / β)
    rw [hu, mul_zero, add_zero] at hfu
    rw [mul_zero, hv, zero_add] at hfv
    rw [hu, hv] at hfuv
    linarith
  let g : ℝ →+ ℝ :=
    { toFun := fun x => f x - f 0
      map_zero' := sub_self _
      map_add' := hadd }
  have hg : Continuous g := hf.sub continuous_const
  intro x
  have hlin := map_real_smul g hg x (1 : ℝ)
  change f (x * 1) - f 0 = x * (f 1 - f 0) at hlin
  rw [mul_one] at hlin
  nlinarith

theorem continuous_weighted_jensen_classification (α β : ℝ) (h : α + β = 1)
    (f : ℝ → ℝ) (hf : Continuous f) :
    (∀ x y : ℝ, f (α * x + β * y) = α * f x + β * f y) ↔
      α = 0 ∨ β = 0 ∨ ∃ a b : ℝ, ∀ x : ℝ, f x = a * x + b := by
  constructor
  · intro hfe
    by_cases hα : α = 0
    · exact Or.inl hα
    by_cases hβ : β = 0
    · exact Or.inr (Or.inl hβ)
    exact Or.inr (Or.inr ⟨f 1 - f 0, f 0, weighted_jensen_affine α β h hα hβ f hf hfe⟩)
  · rintro (hα | hβ | ⟨a, b, hab⟩)
    · have hβ : β = 1 := by linarith
      subst α
      subst β
      simp
    · have hα : α = 1 := by linarith
      subst α
      subst β
      simp
    · intro x y
      rw [hab, hab, hab]
      have hb : (α + β) * b = b := by rw [h, one_mul]
      nlinarith

theorem solution (α β : ℝ) (h : α + β = 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ x y : ℝ, f (α * x + β * y) = α * f x + β * f y := by
  refine ⟨id, continuous_id, ?_⟩
  apply (continuous_weighted_jensen_classification α β h id continuous_id).mpr
  exact Or.inr (Or.inr ⟨1, 0, fun x => by simp⟩)

#print axioms weighted_jensen_affine
#print axioms continuous_weighted_jensen_classification
#print axioms solution
