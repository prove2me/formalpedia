-- Prove2me | solution 1 for FourColor.mirror_minimal_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-30T00:01:38.612904+00:00
-- url     : https://prove2.me/submissions/7824b671-c250-4155-8fa6-9b97ced424e8

import Definitions.Def_FourColor_Reflection

/-!
Orientation reversal preserves the precubic dart-minimal comparison class.
Source: Gonthier (2005), Section 5.1, PDF pp. 19–20, unnumbered hypermap
identity and Euler formula; Section 5.5, PDF pp. 44–48, reflection in matching.
Pinned Rocq commit c1d6b1cd5288bea4b067aac13cdde3c18dffe018:
`hypermap.v:366–375`, `coloring.v:369–378` (`minimal_counter_example_mirror`).
The edge permutation is conjugated, rather than assumed unchanged.
-/

namespace FourColor

namespace Hypermap

private theorem mirror_node_identity {n : ℕ} (H : Hypermap n) (x : Fin n) :
    H.node x = H.edge.symm (H.face.symm x) := by
  simpa using H.edge_node_face (H.edge.symm (H.face.symm x))

private theorem mirror_edge_conjugate {n : ℕ} (H : Hypermap n) :
    H.mirror.edge = H.face * H.edge⁻¹ * H.face⁻¹ := by
  apply Equiv.ext
  intro x
  exact congrArg H.face (mirror_node_identity H x)

private theorem mirror_sameFace {n : ℕ} (H : Hypermap n) (x y : Fin n) :
    H.mirror.SameFace x y ↔ H.SameFace x y := by
  exact Equiv.Perm.sameCycle_inv

private theorem mirror_nodeArity {n : ℕ} (H : Hypermap n) (x : Fin n) :
    H.mirror.nodeArity x = H.nodeArity x := by
  unfold nodeArity
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun y ↦ Equiv.Perm.sameCycle_inv)

private theorem mirror_nodeCount {n : ℕ} (H : Hypermap n) :
    H.mirror.nodeCount = H.nodeCount := by
  apply Nat.card_congr
  exact Quotient.congr (Equiv.refl _) (fun x y ↦ Equiv.Perm.sameCycle_inv)

private theorem mirror_faceCount {n : ℕ} (H : Hypermap n) :
    H.mirror.faceCount = H.faceCount := by
  apply Nat.card_congr
  exact Quotient.congr (Equiv.refl _) (fun x y ↦ Equiv.Perm.sameCycle_inv)

private theorem mirror_edgeCount {n : ℕ} (H : Hypermap n) :
    H.mirror.edgeCount = H.edgeCount := by
  unfold edgeCount
  rw [mirror_edge_conjugate]
  apply Nat.card_congr
  refine Quotient.congr H.face.symm (fun x y ↦ ?_)
  exact Equiv.Perm.sameCycle_conj.trans Equiv.Perm.sameCycle_inv

private theorem mirror_link_forward {n : ℕ} (H : Hypermap n) (x y : Fin n)
    (h : H.mirror.Link x y) : H.SameComponent x y := by
  rcases h with he | hn | hf
  · subst y
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl)))
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inr rfl)))
  · subst y
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact Or.inr (Or.inl (by simp [mirror]))
  · subst y
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact Or.inr (Or.inr (by simp [mirror]))

private theorem mirror_link_backward {n : ℕ} (H : Hypermap n) (x y : Fin n)
    (h : H.Link x y) : H.mirror.SameComponent x y := by
  rcases h with he | hn | hf
  · subst y
    have he : H.edge x = H.face.symm (H.node.symm x) := by
      simpa using congrArg (fun z ↦ H.face.symm (H.node.symm z)) (H.edge_node_face x)
    rw [he]
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl)))
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inr rfl)))
  · subst y
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact Or.inr (Or.inl (by simp [mirror]))
  · subst y
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    exact Or.inr (Or.inr (by simp [mirror]))

private theorem mirror_sameComponent {n : ℕ} (H : Hypermap n) (x y : Fin n) :
    H.mirror.SameComponent x y ↔ H.SameComponent x y := by
  constructor
  · intro h
    induction h with
    | rel a b hab => exact mirror_link_forward H a b hab
    | refl a => exact Relation.EqvGen.refl a
    | symm a b _ ih => exact Relation.EqvGen.symm a b ih
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans a b c ih₁ ih₂
  · intro h
    induction h with
    | rel a b hab => exact mirror_link_backward H a b hab
    | refl a => exact Relation.EqvGen.refl a
    | symm a b _ ih => exact Relation.EqvGen.symm a b ih
    | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans a b c ih₁ ih₂

private theorem mirror_componentCount {n : ℕ} (H : Hypermap n) :
    H.mirror.componentCount = H.componentCount := by
  apply Nat.card_congr
  exact Quotient.congr (Equiv.refl _) (mirror_sameComponent H)

private theorem mirror_planar {n : ℕ} (H : Hypermap n) (h : H.Planar) :
    H.mirror.Planar := by
  simpa [Planar, mirror_edgeCount, mirror_nodeCount, mirror_faceCount,
    mirror_componentCount] using h

private theorem mirror_plain {n : ℕ} (H : Hypermap n) (h : H.Plain) :
    H.mirror.Plain := by
  have hi (x : Fin n) : H.edge.symm x = H.edge x := by
    apply H.edge.injective
    simpa using (h x).1.symm
  intro x
  rw [mirror_edge_conjugate]
  simp only [Equiv.Perm.mul_apply]
  constructor
  · simp [hi, (h (H.face.symm x)).1]
  · intro hx
    have he : H.edge (H.face.symm x) = H.face.symm x := by
      simpa [hi] using congrArg H.face.symm hx
    exact (h (H.face.symm x)).2 he

private theorem mirror_bridgeless {n : ℕ} (H : Hypermap n) (h : H.Bridgeless)
    (hp : H.Plain) : H.mirror.Bridgeless := by
  intro x hx
  have hi (x : Fin n) : H.edge.symm x = H.edge x := by
    apply H.edge.injective
    simpa using (hp x).1.symm
  have hs := (mirror_sameFace H x (H.mirror.edge x)).mp hx
  rw [mirror_edge_conjugate] at hs
  have hs' : H.SameFace (H.face.symm x) (H.edge (H.face.symm x)) := by
    simpa [SameFace, Equiv.Perm.mul_apply, hi] using hs
  exact h (H.face.symm x) hs'

private theorem mirror_coloring_back {n : ℕ} (H : Hypermap n)
    (h : H.mirror.FourColorable) : H.FourColorable := by
  obtain ⟨color, hface, hedge⟩ := h
  refine ⟨color, ?_, ?_⟩
  · intro x y hxy
    exact hface x y ((mirror_sameFace H x y).mpr hxy)
  · intro x hx
    have hn : H.node (H.face (H.edge x)) = x := H.edge_node_face x
    have he : H.mirror.edge (H.face (H.edge x)) = H.face x := by
      simpa [mirror] using congrArg H.face hn
    have hf (y : Fin n) : color (H.face y) = color y := by
      apply hface
      exact (mirror_sameFace H _ _).mpr
        ((Equiv.Perm.SameCycle.refl H.face y).apply_left)
    apply hedge (H.face (H.edge x))
    rw [he, hf, hf]
    exact hx.symm

end Hypermap

end FourColor

open FourColor

theorem solution :
    ∀ (n : ℕ) (H : Hypermap n), H.MinimalCounterexample → H.mirror.MinimalCounterexample := by
  intro n H h
  obtain ⟨hplanar, hbridge, hplain, hprecubic⟩ := h.admissible
  refine ⟨⟨Hypermap.mirror_planar H hplanar,
    Hypermap.mirror_bridgeless H hbridge hplain, Hypermap.mirror_plain H hplain, ?_⟩,
    ?_, h.minimal⟩
  · intro x
    simpa [Hypermap.mirror_nodeArity] using hprecubic x
  · intro hc
    exact h.not_fourColorable (Hypermap.mirror_coloring_back H hc)
