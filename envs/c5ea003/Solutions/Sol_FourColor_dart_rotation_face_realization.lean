-- Prove2me | solution 1 for FourColor.dart_rotation_face_realization
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-28T00:25:15.666207+00:00
-- url     : https://prove2.me/submissions/c0129bc9-e892-4c25-bb9d-d600662ed4b7

import Definitions.Def_FourColor_GraphRotation

namespace FourColor

universe u v

private theorem sameCycle_transport {A : Type u} {B : Type v} (q : A ≃ B)
    (p : Equiv.Perm A) (x y : A) :
    (q.permCongr p).SameCycle (q x) (q y) ↔ p.SameCycle x y := by
  unfold Equiv.Perm.SameCycle
  apply exists_congr
  intro k
  have hpow : (q.permCongr p) ^ k = q.permCongr (p ^ k) :=
    (map_zpow q.permCongrHom p k).symm
  rw [hpow]
  simp

private theorem cycleCount_transport {A : Type u} {B : Type v} (q : A ≃ B)
    (p : Equiv.Perm A) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (q.permCongr p))) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) := by
  exact (Nat.card_congr (Quotient.congr q
    (fun x y ↦ (sameCycle_transport q p x y).symm))).symm

private theorem eqvGen_map {A : Type u} {B : Type v} {r : A → A → Prop}
    {s : B → B → Prop} (f : A → B) (h : ∀ x y, r x y → Relation.EqvGen s (f x) (f y))
    {x y : A} (hxy : Relation.EqvGen r x y) : Relation.EqvGen s (f x) (f y) := by
  induction hxy with
  | rel a b hab => exact h a b hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

namespace DartRotation

variable {V : Type u} {G : SimpleGraph V}

private def toHypermap (R : DartRotation G) {n : ℕ} (q : G.Dart ≃ Fin n) : Hypermap n where
  edge := q.permCongr (dartReverse G)
  node := q.permCongr R.boundary
  face := q.permCongr R.rotate
  edge_node_face x := by
    simp [boundary, dartReverse]

private theorem link_transport (R : DartRotation G) {n : ℕ} (q : G.Dart ≃ Fin n)
    (x y : G.Dart) :
    Relation.EqvGen R.Link x y ↔ (R.toHypermap q).SameComponent (q x) (q y) := by
  constructor
  · apply eqvGen_map q
    intro a b hab
    apply Relation.EqvGen.rel
    rcases hab with h | h
    · exact Or.inl (by simpa [toHypermap] using congrArg q h)
    · exact Or.inr (Or.inr (by simpa [toHypermap] using congrArg q h))
  · intro h
    have h' := eqvGen_map q.symm (r := (R.toHypermap q).Link) (s := R.Link) ?_ h
    · simpa using h'
    intro a b hab
    rcases hab with h | h | h
    · apply Relation.EqvGen.rel
      exact Or.inl (by simpa [toHypermap] using congrArg q.symm h)
    · have hb : R.boundary (q.symm a) = q.symm b := by
        simpa [toHypermap] using congrArg q.symm h
      have hrot : Relation.EqvGen R.Link (q.symm a) (R.rotate⁻¹ (q.symm a)) := by
        apply Relation.EqvGen.symm
        apply Relation.EqvGen.rel
        exact Or.inr (by simp)
      apply Relation.EqvGen.trans _ _ _ hrot
      apply Relation.EqvGen.rel
      exact Or.inl hb
    · apply Relation.EqvGen.rel
      exact Or.inr (by simpa [toHypermap] using congrArg q.symm h)

end DartRotation

end FourColor

open FourColor
universe u

/-- Finite algebraic bridge for graph realization. Source: Gonthier (2005), Section 5.1,
PDF pp. 18–20, reciprocal darts, circular lists, triangular identity and unnumbered Euler
formula. The geometric existence of the rotation is not assumed as part of this proof. -/
theorem solution :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V) (R : DartRotation G), R.EulerPlanar →
      ∃ (n : ℕ) (H : Hypermap n), H.Planar ∧ H.Plain ∧ Nonempty (FaceRepresentation G H) := by
  intro V _ G R hplanar
  classical
  letI : Fintype V := Fintype.ofFinite V
  let q : G.Dart ≃ Fin (Fintype.card G.Dart) := Fintype.equivFin G.Dart
  let H := R.toHypermap q
  refine ⟨Fintype.card G.Dart, H, ?_, ?_, ?_⟩
  · have he := cycleCount_transport q (dartReverse G)
    have hn := cycleCount_transport q R.boundary
    have hf := cycleCount_transport q R.rotate
    have hc := Nat.card_congr (Quotient.congr
      (ra := Relation.EqvGen.setoid R.Link)
      (rb := Relation.EqvGen.setoid H.Link) q (R.link_transport q))
    unfold Hypermap.Planar Hypermap.edgeCount Hypermap.nodeCount Hypermap.faceCount
      Hypermap.componentCount
    change Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (q.permCongr (dartReverse G)))) +
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (q.permCongr R.boundary))) +
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (q.permCongr R.rotate))) = _
    rw [he, hn, hf, ← hc]
    simpa [DartRotation.EulerPlanar, Nat.card_eq_fintype_card] using hplanar
  · intro x
    constructor
    · simp [H, DartRotation.toHypermap, dartReverse]
    · intro h
      have heq : (q.symm x).symm = q.symm x := by
        simpa [H, DartRotation.toHypermap, dartReverse] using congrArg q.symm h
      exact (q.symm x).symm_ne heq
  · refine ⟨{ vertexOf := fun x ↦ (q.symm x).fst, sameFace_iff := ?_, adj_iff := ?_ }⟩
    · intro x y
      have h := sameCycle_transport q R.rotate (q.symm x) (q.symm y)
      simpa [H, DartRotation.toHypermap, Hypermap.SameFace] using
        h.trans (R.sameCycle_iff _ _)
    · intro v w
      constructor
      · intro hvw
        refine ⟨q ⟨(v, w), hvw⟩, ?_, ?_⟩
        · simp
        · simp [H, DartRotation.toHypermap, dartReverse]
      · rintro ⟨x, rfl, hw⟩
        have hw' : (q.symm x).snd = w := by
          simpa [H, DartRotation.toHypermap, dartReverse] using hw
        rw [← hw']
        exact (q.symm x).adj

