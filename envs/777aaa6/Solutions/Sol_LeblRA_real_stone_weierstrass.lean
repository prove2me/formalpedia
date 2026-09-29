-- Prove2me | solution 1 for LeblRA.real_stone_weierstrass
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:13:52.664058+00:00
-- url     : https://prove2.me/submissions/dea55757-6520-48cd-b793-d62e192532b7

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA

private theorem interpolate {K X B : Type*} [Field K] [CommRing B] [Algebra K B]
    (A : NonUnitalSubalgebra K B) (E : B →ₐ[K] (X → K))
    (sep : ∀ x y : X, x ≠ y → ∃ g ∈ A, E g x ≠ E g y)
    (nv : ∀ x : X, ∃ g ∈ A, E g x ≠ 0)
    (x y : X) (hxy : x ≠ y) (c d : K) :
    ∃ f ∈ A, E f x = c ∧ E f y = d := by
  obtain ⟨g, hg, hsep⟩ := sep x y hxy
  obtain ⟨h, hh, hx⟩ := nv x
  obtain ⟨k, hk, hy⟩ := nv y
  let u := g * h - (E g y) • h
  let v := g * k - (E g x) • k
  have hu : u ∈ A := A.sub_mem (A.mul_mem hg hh) (A.smul_mem _ hh)
  have hv : v ∈ A := A.sub_mem (A.mul_mem hg hk) (A.smul_mem _ hk)
  refine ⟨(c / ((E g x - E g y) * E h x)) • u +
    (d / ((E g y - E g x) * E k y)) • v,
    A.add_mem (A.smul_mem _ hu) (A.smul_mem _ hv), ?_, ?_⟩
  · simp only [map_add, map_smul, map_sub, map_mul, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, Pi.mul_apply, smul_eq_mul, u, v]
    field_simp [sub_ne_zero.mpr hsep, sub_ne_zero.mpr hsep.symm, hx, hy]
    ring
  · simp only [map_add, map_smul, map_sub, map_mul, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, Pi.mul_apply, smul_eq_mul, u, v]
    field_simp [sub_ne_zero.mpr hsep, sub_ne_zero.mpr hsep.symm, hx, hy]
    ring

private theorem strong_separation {K X : Type*} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] [TopologicalSpace X]
    (A : NonUnitalSubalgebra K C(X, K))
    (sep : ∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y)
    (nv : ∀ x : X, ∃ g ∈ A, g x ≠ 0) :
    (A : Set C(X, K)).SeparatesPointsStrongly := by
  intro v x y
  by_cases hxy : x = y
  · subst y
    obtain ⟨g, hg, hx⟩ := nv x
    refine ⟨(v x / g x) • g, A.smul_mem _ hg, ?_, ?_⟩
    all_goals simpa only [ContinuousMap.smul_apply, smul_eq_mul] using div_mul_cancel₀ (v x) hx
  · exact interpolate A (ContinuousMap.coeFnAlgHom K) sep nv x y hxy (v x) (v y)

private theorem abs_mem_closed {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : NonUnitalSubalgebra ℝ C(X, ℝ)) (hA : IsClosed (A : Set C(X, ℝ)))
    (f : C(X, ℝ)) (hf : f ∈ A) : |f| ∈ A := by
  let s : Set ℝ := Set.Icc (-‖f‖) ‖f‖
  letI : Fact ((0 : ℝ) ∈ s) := ⟨⟨neg_nonpos.mpr (norm_nonneg f), norm_nonneg f⟩⟩
  let g : C(s, ℝ)₀ := ⟨⟨fun x => |(x : ℝ)|, continuous_abs.comp continuous_subtype_val⟩, by change |(0 : ℝ)| = 0; exact abs_zero⟩
  let F : C(s, ℝ)₀ → C(X, ℝ) := fun q => (q : C(s, ℝ)).comp (ContinuousMap.attachBound f)
  have hF : Continuous F := by
    exact (ContinuousMap.compRightContinuousMap ℝ (ContinuousMap.attachBound f)).continuous.comp
      ContinuousMapZero.isEmbedding_toContinuousMap.continuous
  have h : ∀ q : C(s, ℝ)₀, F q ∈ A := by
    intro q
    induction q using ContinuousMapZero.induction_on_of_compact with
    | zero => exact A.zero_mem
    | id => simpa [F] using hf
    | star_id => simpa [F] using hf
    | add q r hq hr => simpa [F] using A.add_mem hq hr
    | mul q r hq hr => simpa [F] using A.mul_mem hq hr
    | smul r q hq => simpa [F] using A.smul_mem r hq
    | frequently q hq => exact hq.mem_of_closed (hA.preimage hF)
  exact h g

theorem _root_.solution {X : Type*} [MetricSpace X] [CompactSpace X]
    (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (sep : ∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y)
    (nv : ∀ x : X, ∃ g ∈ A, g x ≠ 0) :
    closure (A : Set C(X, ℝ)) = Set.univ := by
  let B := A.topologicalClosure
  have hc : IsClosed (B : Set C(X, ℝ)) := A.isClosed_topologicalClosure
  have habs (f : C(X, ℝ)) (hf : f ∈ B) : |f| ∈ B := abs_mem_closed B hc f hf
  have hinf (f : C(X, ℝ)) (hf : f ∈ B) (g : C(X, ℝ)) (hg : g ∈ B) : f ⊓ g ∈ B := by
    rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
    exact B.smul_mem _ (B.sub_mem (B.add_mem hf hg) (habs _ (B.sub_mem hg hf)))
  have hsup (f : C(X, ℝ)) (hf : f ∈ B) (g : C(X, ℝ)) (hg : g ∈ B) : f ⊔ g ∈ B := by
    rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
    exact B.smul_mem _ (B.add_mem (B.add_mem hf hg) (habs _ (B.sub_mem hg hf)))
  have hstrong : (B : Set C(X, ℝ)).SeparatesPointsStrongly := by
    intro v x y
    obtain ⟨f, hf, hfx, hfy⟩ := strong_separation A sep nv v x y
    exact ⟨f, A.le_topologicalClosure hf, hfx, hfy⟩
  have result := ContinuousMap.sublattice_closure_eq_top (B : Set C(X, ℝ))
    ⟨0, B.zero_mem⟩ hinf hsup hstrong
  rwa [hc.closure_eq] at result

end LeblRA
