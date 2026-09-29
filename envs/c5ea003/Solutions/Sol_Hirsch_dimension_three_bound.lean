-- Prove2me | solution 1 for Hirsch.dimension_three_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T02:06:51.066496+00:00
-- url     : https://prove2.me/submissions/f64e52e2-5325-441e-9f30-1ecf6fcdd563

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_dimension_two_bound
import Theorems.Thm_Hirsch_klee_three_dimensional_bound

open scoped RealInnerProductSpace
open Hirsch

namespace HirschLib

/-! ## Walks -/

/-- A constant walk witnesses `DiamLE` between equal endpoints. -/
theorem diamLE_of_subsingleton {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v) :
    DiamLE P B := by
  intro u hu v hv
  exact ⟨fun _ => u, rfl, h u hu v hv, fun i _ => Or.inl rfl⟩

/-- One edge, then stay put: a walk of any positive length. -/
theorem diamLE_of_adj {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) (B : ℕ)
    (hB : 1 ≤ B)
    (h : ∀ u ∈ Set.extremePoints ℝ P, ∀ v ∈ Set.extremePoints ℝ P, u = v ∨ Adj P u v) :
    DiamLE P B := by
  intro u hu v hv
  rcases h u hu v hv with heq | hadj
  · exact ⟨fun _ => u, rfl, heq, fun i _ => Or.inl rfl⟩
  · have hB0 : B ≠ 0 := by omega
    refine ⟨fun i => if i = 0 then u else v, by simp, by simp [hB0], ?_⟩
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact Or.inr (by simpa using hadj)
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i + 1 ≠ 0 := by omega
      left; simp [hi0, hi1]

/-! ## Convex sets in a space of dimension at most one -/

/-- In a space of dimension at most one, a convex set with two distinct extreme
points is exactly the segment between them. -/
theorem eq_segment_of_finrank_le_one {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (h1 : Module.finrank ℝ E ≤ 1) (P : Set E) (hP : Convex ℝ P)
    {u v : E} (hu : u ∈ Set.extremePoints ℝ P) (hv : v ∈ Set.extremePoints ℝ P)
    (huv : u ≠ v) : P = segment ℝ u v := by
  classical
  set e : E := v - u with he
  have hene : e ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  -- the line through `u` and `v` is everything
  have hspan : Submodule.span ℝ ({e} : Set E) = ⊤ := by
    have h2 : Module.finrank ℝ (Submodule.span ℝ ({e} : Set E)) = 1 :=
      finrank_span_singleton hene
    have h3 : 1 ≤ Module.finrank ℝ E := h2 ▸ Submodule.finrank_le _
    exact Submodule.eq_top_of_finrank_eq (by omega)
  have hline : ∀ x : E, ∃ t : ℝ, x = u + t • e := by
    intro x
    have : x - u ∈ Submodule.span ℝ ({e} : Set E) := by rw [hspan]; trivial
    rw [Submodule.mem_span_singleton] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht]; abel⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, rfl⟩ := hline x
    have hvu : v = u + (1:ℝ) • e := by rw [he]; module
    -- `t < 0` would exhibit `u` inside an open segment of `P`
    have ht0 : 0 ≤ t := by
      by_contra hlt
      push_neg at hlt
      have hden : (0:ℝ) < 1 - t := by linarith
      refine huv (((mem_extremePoints.mp hu).2 _ hx _ (extremePoints_subset hv) ?_).2).symm
      refine ⟨1 / (1 - t), -t / (1 - t), div_pos one_pos hden,
        div_pos (by linarith) hden, by field_simp <;> ring, ?_⟩
      have h1 : (1:ℝ) / (1 - t) + -t / (1 - t) = 1 := by field_simp <;> ring
      have h2 : (1:ℝ) / (1 - t) * t + (-t / (1 - t)) * 1 = 0 := by field_simp <;> ring
      rw [hvu]
      calc (1 / (1 - t)) • (u + t • e) + (-t / (1 - t)) • (u + (1:ℝ) • e)
          = ((1:ℝ) / (1 - t) + -t / (1 - t)) • u
            + ((1:ℝ) / (1 - t) * t + (-t / (1 - t)) * 1) • e := by module
        _ = u := by rw [h1, h2]; module
    -- `t > 1` would exhibit `v` inside an open segment of `P`
    have ht1 : t ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have hden : (0:ℝ) < t := by linarith
      refine huv (((mem_extremePoints.mp hv).2 _ (extremePoints_subset hu) _ hx ?_).1)
      refine ⟨(t - 1) / t, 1 / t, div_pos (by linarith) hden, div_pos one_pos hden,
        by field_simp <;> ring, ?_⟩
      have h1 : (t - 1) / t + 1 / t * 1 = 1 := by field_simp <;> ring
      have h2 : (1:ℝ) / t * t = 1 := by field_simp <;> ring
      rw [hvu]
      calc ((t - 1) / t) • u + (1 / t) • (u + t • e)
          = ((t - 1) / t + 1 / t * 1) • u + ((1:ℝ) / t * t) • e := by module
        _ = u + (1:ℝ) • e := by rw [h1, h2]; module
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    rw [he]; module
  · exact hP.segment_subset (extremePoints_subset hu) (extremePoints_subset hv)


/-! ## H-polytopes -/

theorem hpoly_convex {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ) :
    Convex ℝ (Hpoly a b) := by
  intro x hx y hy s t hs ht hst i
  have h1 := hx i
  have h2 := hy i
  have hexp : ⟪a i, s • x + t • y⟫ = s * ⟪a i, x⟫ + t * ⟪a i, y⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [hexp]
  have e1 : s * ⟪a i, x⟫ ≤ s * b i := mul_le_mul_of_nonneg_left h1 hs
  have e2 : t * ⟪a i, y⟫ ≤ t * b i := mul_le_mul_of_nonneg_left h2 ht
  have e3 : s * b i + t * b i = b i := by rw [← add_mul, hst, one_mul]
  linarith

/-- If the polytope is bounded, every nonzero direction is cut off by some
inequality: no ray can survive inside a bounded set. -/
theorem exists_pos_inner_of_bounded {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) (e : EuclideanSpace ℝ (Fin d)) (he : e ≠ 0) :
    ∃ i, 0 < ⟪a i, e⟫ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbd
  have hepos : (0:ℝ) < ‖e‖ := norm_pos_iff.mpr he
  set t : ℝ := (R + ‖x0‖ + 1) / ‖e‖ with htdef
  have hRnn : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hx0)
  have ht : 0 ≤ t := by rw [htdef]; positivity
  have hmem : x0 + t • e ∈ Hpoly a b := by
    intro i
    have hexp : ⟪a i, x0 + t • e⟫ = ⟪a i, x0⟫ + t * ⟪a i, e⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    rw [hexp]
    have h1 := hx0 i
    nlinarith [hcon i]
  have h1 := hR _ hmem
  have hnorm : ‖t • e‖ ≤ ‖x0 + t • e‖ + ‖x0‖ := by
    calc ‖t • e‖ = ‖(x0 + t • e) - x0‖ := by congr 1; abel
      _ ≤ ‖x0 + t • e‖ + ‖x0‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hnorm
  have hte : t * ‖e‖ = R + ‖x0‖ + 1 := by
    rw [htdef]; field_simp
  linarith

/-- In dimension at least one, a bounded nonempty H-polytope needs at least two
inequalities: one to cut off each of two opposite directions. -/
theorem two_le_of_bounded {d n : ℕ} (hd : 1 ≤ d) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (hne : (Hpoly a b).Nonempty)
    (hbd : Bornology.IsBounded (Hpoly a b)) : 2 ≤ n := by
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ (1:ℝ) with hedef
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x ⟨0, hd⟩) h
    simp [hedef] at this
  obtain ⟨i, hi⟩ := exists_pos_inner_of_bounded a b hne hbd e he
  obtain ⟨j, hj⟩ := exists_pos_inner_of_bounded a b hne hbd (-e) (neg_ne_zero.mpr he)
  rw [inner_neg_right] at hj
  have hij : i ≠ j := by
    intro h; subst h; linarith
  haveI : Nontrivial (Fin n) := ⟨i, j, hij⟩
  have hcard := Fintype.one_lt_card_iff_nontrivial.mpr ‹Nontrivial (Fin n)›
  simpa using hcard

/-- **The Hirsch bound in dimension at most one.**  For `d = 0` the polytope is a
point; for `d = 1` it is a segment, its two extreme points are joined by the single
edge `P` itself, and boundedness forces `n ≥ 2`, so one step is available. -/
theorem dim_le_one_bound {d n : ℕ} (hd : d ≤ 1)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · refine diamLE_of_subsingleton _ _ fun u _ v _ => ?_
    exact Subsingleton.elim u v
  · have hd1' : d = 1 := le_antisymm hd hd1
    subst hd1'
    have h2 : 2 ≤ n := two_le_of_bounded le_rfl a b hne hbd
    refine diamLE_of_adj _ _ (by omega) fun u hu v hv => ?_
    by_cases huv : u = v
    · exact Or.inl huv
    · refine Or.inr ⟨huv, ?_⟩
      have hrk : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) ≤ 1 := by simp
      have hseg := eq_segment_of_finrank_le_one hrk _ (hpoly_convex a b) hu hv huv
      rw [← hseg]
      exact IsExtreme.refl ℝ _

end HirschLib


open HirschLib

theorem solution (d n : ℕ) (hd : d ≤ 3)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact dim_le_one_bound (by omega) a b hne hbd
  · exact dim_le_one_bound le_rfl a b hne hbd
  · exact Hirsch.dimension_two_bound n a b hne hbd
  · exact Hirsch.klee_three_dimensional_bound n a b hne hbd
