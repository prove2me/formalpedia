-- Prove2me | solution 1 for MovingSofa.exposedEdge_eq_segment_edgeVertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:17:15.631001+00:00
-- url     : https://prove2.me/submissions/73f152d9-1c57-4907-8c15-5634cc667b81

import Mathlib
import Definitions.Def_MovingSofa_Geometry_Basic
import Definitions.Def_MovingSofa_Geometry_Plane
import Definitions.Def_MovingSofa_Geometry_Contacts

noncomputable section

namespace EdgeAux
open MovingSofa

theorem bdd (K : ConvexBody Point) (v : Point) :
    BddAbove ((fun p : Point ↦ inner ℝ p v) '' (K : Set Point)) :=
  (K.isCompact.image (by fun_prop)).bddAbove

theorem inner_le_sv (K : ConvexBody Point) {p : Point}
    (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t :=
  le_csSup (bdd K _) ⟨p, hp, rfl⟩

theorem decomp (p : Point) (t : Real.Angle) :
    p = inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t := by
  have h := Real.Angle.cos_sq_add_sin_sq t
  ext i
  fin_cases i
  · simp [normalVector, tangentVector, frame, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two]
    linear_combination (-(p 0) * h)
  · simp [normalVector, tangentVector, frame, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two]
    linear_combination (-(p 1) * h)

theorem edge_nonempty (K : ConvexBody Point) (t : Real.Angle) : (exposedEdge K t).Nonempty := by
  have hcont : Continuous fun p : Point ↦ inner ℝ p (normalVector t) := by fun_prop
  obtain ⟨p, hp, hmax⟩ := K.isCompact.exists_isMaxOn K.nonempty hcont.continuousOn
  refine ⟨p, hp, ?_⟩
  show inner ℝ p (normalVector t) = supportValue K t
  apply le_antisymm (inner_le_sv K hp t)
  exact csSup_le ⟨_, p, hp, rfl⟩ (by rintro _ ⟨q, hq, rfl⟩; exact hmax hq)

theorem edge_compact (K : ConvexBody Point) (t : Real.Angle) : IsCompact (exposedEdge K t) := by
  apply K.isCompact.inter_right
  exact isClosed_eq (by fun_prop) continuous_const

theorem mem_edge_of (K : ConvexBody Point) (t : Real.Angle) (q : Point)
    (hq : q ∈ exposedEdge K t) :
    q = supportValue K t • normalVector t + inner ℝ q (tangentVector t) • tangentVector t := by
  have h2 : inner ℝ q (normalVector t) = supportValue K t := hq.2
  conv_lhs => rw [decomp q t]
  rw [h2]

theorem fst_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t := by
  have hc := (edge_compact K t).image (f := fun p : Point ↦ inner ℝ p (tangentVector t)) (by fun_prop)
  have hne := (edge_nonempty K t).image (fun p : Point ↦ inner ℝ p (tangentVector t))
  obtain ⟨q, hq, hqe⟩ := hc.sSup_mem hne
  have := mem_edge_of K t q hq
  simp only [edgeVertices]
  rw [← hqe, ← this]
  exact hq

theorem snd_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).2 ∈ exposedEdge K t := by
  have hc := (edge_compact K t).image (f := fun p : Point ↦ inner ℝ p (tangentVector t)) (by fun_prop)
  have hne := (edge_nonempty K t).image (fun p : Point ↦ inner ℝ p (tangentVector t))
  obtain ⟨q, hq, hqe⟩ := hc.sInf_mem hne
  have := mem_edge_of K t q hq
  simp only [edgeVertices]
  rw [← hqe, ← this]
  exact hq

end EdgeAux

open MovingSofa EdgeAux in
theorem solution (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t = segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  set n := normalVector t
  set τ := tangentVector t
  set c := supportValue K t
  set H := (fun p : Point ↦ inner ℝ p τ) '' exposedEdge K t with hH
  have hc := (edge_compact K t).image (f := fun p : Point ↦ inner ℝ p τ) (by fun_prop)
  have hne := (edge_nonempty K t).image (fun p : Point ↦ inner ℝ p τ)
  have hv1 : (edgeVertices K t).1 = c • n + sSup H • τ := rfl
  have hv2 : (edgeVertices K t).2 = c • n + sInf H • τ := rfl
  have hconv : Convex ℝ (exposedEdge K t) := by
    intro x hx y hy a b ha hb hab
    refine ⟨K.convex hx.1 hy.1 ha hb hab, ?_⟩
    have h1 : inner ℝ x n = c := hx.2
    have h2 : inner ℝ y n = c := hy.2
    show inner ℝ (a • x + b • y) n = c
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h1, h2]
    linear_combination c * hab
  apply Set.Subset.antisymm
  · intro q hq
    have hq' := mem_edge_of K t q hq
    have hs1 : inner ℝ q τ ≤ sSup H := le_csSup hc.bddAbove ⟨q, hq, rfl⟩
    have hs2 : sInf H ≤ inner ℝ q τ := csInf_le hc.bddBelow ⟨q, hq, rfl⟩
    rw [hv1, hv2]
    set s := inner ℝ q τ
    set m := sInf H
    set M := sSup H
    rcases eq_or_lt_of_le (hs2.trans hs1) with hmM | hmM
    · have : s = m := le_antisymm (hmM ▸ hs1) hs2
      rw [hq', this]
      exact left_mem_segment ℝ _ _
    · refine ⟨(M - s) / (M - m), (s - m) / (M - m), div_nonneg (by linarith) (by linarith),
        div_nonneg (by linarith) (by linarith), by field_simp; ring, ?_⟩
      rw [hq']
      have hne' : M - m ≠ 0 := by linarith
      ext i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp
      ring
  · exact hconv.segment_subset (snd_mem K t) (fst_mem K t)
