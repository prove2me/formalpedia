-- Prove2me | solution 1 for Hirsch.generic_fibre_objectives_without_independent_ties
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T02:15:25.071601+00:00
-- url     : https://prove2.me/submissions/4ac637cb-f9c4-47fe-9bc2-8d435e539177

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-!
Generic objective segments inside prescribed finite endpoint cones.
UNCOMPILED candidate. This supplies the missing no-independent-ties existence
step, not the affine-envelope count or core-edge bridge already owned by
#239/#240. Endpoint cones are preserved, not assumed generic.
-/

private theorem finite_perturbation
    {I : Type*} [Fintype I] (a b : I → ℝ) :
    ∃ t : ℝ, 0 < t ∧
      (∀ i, a i < 0 → a i + t * b i < 0) ∧
      (∀ i, a i ≠ 0 ∨ b i ≠ 0 → a i + t * b i ≠ 0) := by
  classical
  let radius : Option I → ℝ := fun i => match i with
    | none => 1
    | some i => if a i = 0 then 1 else |a i| / (2 * (|b i| + 1))
  have hr : ∀ i, 0 < radius i := by
    intro i
    cases i with
    | none => norm_num [radius]
    | some i =>
      dsimp [radius]
      split_ifs with hi
      · norm_num
      · exact div_pos (abs_pos.mpr hi) (by positivity)
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Option I)) radius ⟨none, Finset.mem_univ _⟩
  let t := radius i₀
  have ht : 0 < t := hr i₀
  have hsmall : ∀ i, a i ≠ 0 → |t * b i| < |a i| := by
    intro i hi
    have hle : t ≤ |a i| / (2 * (|b i| + 1)) := by
      simpa only [radius, if_neg hi] using hmin (some i) (Finset.mem_univ _)
    have hprod : t * (2 * (|b i| + 1)) ≤ |a i| :=
      (le_div_iff₀ (by positivity)).mp hle
    rw [abs_mul, abs_of_pos ht]
    have hb : 0 ≤ |b i| := abs_nonneg _
    have hnon := mul_nonneg ht.le hb
    nlinarith
  refine ⟨t, ht, ?_, ?_⟩
  · intro i hi
    have h := hsmall i (ne_of_lt hi)
    rw [abs_of_neg hi] at h
    have hb := le_abs_self (t * b i)
    linarith
  · intro i hi
    by_cases ha : a i = 0
    · have hb : b i ≠ 0 := hi.resolve_left (not_not.mpr ha)
      simpa only [ha, zero_add] using mul_ne_zero (ne_of_gt ht) hb
    · intro he
      have hab : |t * b i| = |a i| := by
        have hneg : t * b i = -a i := by linarith
        rw [hneg, abs_neg]
      exact (ne_of_lt (hsmall i ha)) hab

private theorem avoiding_preserving_comparisons
    {E I J : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] [Fintype J]
    (f₀ : E →ₗ[ℝ] ℝ) (c : I → E) (v : J → E)
    (hc : ∀ i, f₀ (c i) < 0) (hv : ∀ j, v j ≠ 0) :
    ∃ f : E →ₗ[ℝ] ℝ,
      (∀ i, f (c i) < 0) ∧ (∀ j, f (v j) ≠ 0) := by
  classical
  obtain ⟨h, hh⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℝ) v hv
  let w : I ⊕ J → E := Sum.elim c v
  obtain ⟨t, ht, hneg, hne⟩ :=
    finite_perturbation (fun i => f₀ (w i)) (fun i => h (w i))
  refine ⟨f₀ + t • h, ?_, ?_⟩
  · intro i
    exact hneg (.inl i) (hc i)
  · intro j
    exact hne (.inr j) (Or.inr (hh j))

private theorem two_affine_zeros_force_determinant
    (a b c d t : ℝ) (ha : a ≠ 0)
    (hi : (1-t)*a+t*b=0) (hj : (1-t)*c+t*d=0) : a*d-c*b=0 := by
  have ht : t ≠ 0 := by
    intro ht
    have hz : a = 0 := by simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hi
    exact ha hz
  have he : t*(a*d-c*b)=0 := by
    linear_combination a*hj-c*hi
  exact (mul_eq_zero.mp he).resolve_left ht

/-- Any two nonempty finite strict endpoint cones have an objective segment
that never annihilates two linearly independent listed difference vectors.
Every endpoint comparison is preserved. No normal-fan genericity oracle,
full-dimensionality, or probabilistic assumption is supplied. -/
theorem solution
    {E A B I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype A] [Fintype B] [Fintype I]
    (f₀ g₀ : E →ₗ[ℝ] ℝ) (c₀ : A → E) (c₁ : B → E) (v : I → E)
    (hc₀ : ∀ a, f₀ (c₀ a) < 0)
    (hc₁ : ∀ b, g₀ (c₁ b) < 0)
    (hv : ∀ i, v i ≠ 0) :
    ∃ f g : E →ₗ[ℝ] ℝ,
      (∀ a, f (c₀ a) < 0) ∧
      (∀ b, g (c₁ b) < 0) ∧
      (∀ i, f (v i) ≠ 0) ∧
      (∀ i, g (v i) ≠ 0) ∧
      (∀ i j, v j ∉ Submodule.span ℝ ({v i} : Set E) →
        f (v i)*g (v j)-f (v j)*g (v i) ≠ 0) ∧
      ∀ (t : ℝ) (i j : I),
        ((1-t)*f (v i)+t*g (v i)=0) →
        ((1-t)*f (v j)+t*g (v j)=0) →
        v j ∈ Submodule.span ℝ ({v i} : Set E) := by
  classical
  obtain ⟨f, hfc, hfv⟩ := avoiding_preserving_comparisons f₀ c₀ v hc₀ hv
  let Bad := {ij : I × I // v ij.2 ∉ Submodule.span ℝ ({v ij.1} : Set E)}
  let d : Bad → E := fun ij =>
    f (v ij.1.1) • v ij.1.2 - f (v ij.1.2) • v ij.1.1
  have hd : ∀ ij, d ij ≠ 0 := by
    intro ij hz
    have he : f (v ij.1.1) • v ij.1.2 = f (v ij.1.2) • v ij.1.1 :=
      sub_eq_zero.mp hz
    let W : Submodule ℝ E := Submodule.span ℝ ({v ij.1.1} : Set E)
    have hm : f (v ij.1.1) • v ij.1.2 ∈ W := by
      rw [he]
      exact W.smul_mem _ (Submodule.subset_span (by simp))
    exact ij.2 ((W.smul_mem_iff (hfv ij.1.1)).mp hm)
  let all : I ⊕ Bad → E := Sum.elim v d
  have hall : ∀ q, all q ≠ 0 := by
    intro q
    cases q with
    | inl i => exact hv i
    | inr ij => exact hd ij
  obtain ⟨g, hgc, hgv⟩ := avoiding_preserving_comparisons g₀ c₁ all hc₁ hall
  have hdet : ∀ i j, v j ∉ Submodule.span ℝ ({v i} : Set E) →
      f (v i)*g (v j)-f (v j)*g (v i) ≠ 0 := by
    intro i j hij
    have hh := hgv (.inr ⟨(i,j),hij⟩)
    change g (f (v i) • v j - f (v j) • v i) ≠ 0 at hh
    simpa only [map_sub, map_smul, smul_eq_mul] using hh
  refine ⟨f, g, hfc, hgc, hfv, (fun i => hgv (.inl i)), hdet, ?_⟩
  intro t i j hi hj
  by_contra hij
  exact hdet i j hij (two_affine_zeros_force_determinant
    (f (v i)) (g (v i)) (f (v j)) (g (v j)) t (hfv i) hi hj)

/-- Common strict comparisons, including a fixed core vertex's support cone,
remain strict throughout the closed objective interval. -/
theorem Hirsch.common_strict_comparison_preserved
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f g : E →ₗ[ℝ] ℝ) (x : E) (hf : f x < 0) (hg : g x < 0)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    ((1-t) • f + t • g) x < 0 := by
  change (1-t)*f x+t*g x < 0
  by_cases ht : t = 0
  · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hf
  · exact add_neg_of_nonpos_of_neg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht₁) hf.le)
      (mul_neg_of_pos_of_neg (lt_of_le_of_ne ht₀ (Ne.symm ht)) hg)

#print axioms finite_perturbation
#print axioms avoiding_preserving_comparisons
#print axioms two_affine_zeros_force_determinant
#print axioms solution
#print axioms Hirsch.common_strict_comparison_preserved
