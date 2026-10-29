-- Prove2me | solution 1 for MovingSofa.edgeVertices_fst_mem
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:16:54.938812+00:00
-- url     : https://prove2.me/submissions/fa8bc0b7-5fe2-47da-a01d-51a16394d9f1

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
theorem solution (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t :=
  fst_mem K t
