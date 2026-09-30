-- Prove2me | solution 1 for FourColor.cubic_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-30T01:32:19.830394+00:00
-- url     : https://prove2.me/submissions/9e41c4e0-2aa9-4241-adb1-f76a835c9437

import Definitions.Def_FourColor_Hypermap
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.DeriveFintype

/-!
# Sixfold cubification

The six tags and permutation tables are adapted from `cube.v` in
rocq-community/fourcolor, commit `c1d6b1cd5288bea4b067aac13cdde3c18dffe018`.
Original copyright (2006–2018) Microsoft Corporation and INRIA; distributed under
CeCILL-B (see `missions/four-color-theorem/data/LICENSE.fourcolor`).
Mathematical source: Gonthier (2005), Section 5.1, PDF p. 26, unnumbered
cubification paragraph, and Section 3, PDF p. 6, cubic reduction paragraph.
The equivalence to `Fin (6 * n)` only transports the finite carrier.
-/

namespace FourColor.Cubification

inductive Tag | n | en | f | nf | e | fe
  deriving DecidableEq, Fintype

abbrev Dart (n : ℕ) := Tag × Fin n

variable {n : ℕ}

theorem node_face_eq_edge_inv (H : Hypermap n) (x : Fin n) :
    H.node (H.face x) = H.edge.symm x := by
  simpa using H.edge_node_face (H.edge.symm x)

theorem face_edge_eq_node_inv (H : Hypermap n) (x : Fin n) :
    H.face (H.edge x) = H.node.symm x := by
  apply H.node.injective
  simp [H.edge_node_face]

theorem edge_node_face (H : Hypermap n) (x : Fin n) :
    H.edge (H.node (H.face x)) = x := by
  rw [node_face_eq_edge_inv, Equiv.apply_symm_apply]

theorem face_edge_node (H : Hypermap n) (x : Fin n) :
    H.face (H.edge (H.node x)) = x := by
  rw [face_edge_eq_node_inv, Equiv.symm_apply_apply]

def edgeFn (H : Hypermap n) : Dart n → Dart n
  | (.n, x) => (.fe, x)
  | (.en, x) => (.nf, H.edge x)
  | (.f, x) => (.e, H.node (H.face x))
  | (.nf, x) => (.en, H.node (H.face x))
  | (.e, x) => (.f, H.edge x)
  | (.fe, x) => (.n, x)

def nodeFn (H : Hypermap n) : Dart n → Dart n
  | (.n, x) => (.en, H.node x)
  | (.en, x) => (.fe, x)
  | (.f, x) => (.nf, H.edge x)
  | (.nf, x) => (.e, H.node (H.face x))
  | (.e, x) => (.f, x)
  | (.fe, x) => (.n, H.face (H.edge x))

def faceFn (H : Hypermap n) : Dart n → Dart n
  | (.n, x) => (.en, x)
  | (.en, x) => (.f, x)
  | (.f, x) => (.nf, x)
  | (.nf, x) => (.n, H.face x)
  | (.e, x) => (.e, H.edge x)
  | (.fe, x) => (.fe, H.node x)

theorem edgeFn_involutive (H : Hypermap n) : Function.Involutive (edgeFn H) := by
  rintro ⟨t, x⟩
  cases t <;> simp [edgeFn, H.edge_node_face, edge_node_face]

theorem nodeFn_period_three (H : Hypermap n) (a : Dart n) :
    nodeFn H (nodeFn H (nodeFn H a)) = a := by
  rcases a with ⟨t, x⟩
  cases t <;> simp [nodeFn, H.edge_node_face, edge_node_face, face_edge_node]

theorem edgeFn_ne (H : Hypermap n) (a : Dart n) : edgeFn H a ≠ a := by
  rcases a with ⟨t, x⟩
  cases t <;> simp [edgeFn]

theorem nodeFn_ne (H : Hypermap n) (a : Dart n) : nodeFn H a ≠ a := by
  rcases a with ⟨t, x⟩
  cases t <;> simp [nodeFn]

theorem nodeFn_two_ne (H : Hypermap n) (a : Dart n) :
    nodeFn H (nodeFn H a) ≠ a := by
  rcases a with ⟨t, x⟩
  cases t <;> simp [nodeFn]

def edgePerm (H : Hypermap n) : Equiv.Perm (Dart n) :=
  ⟨edgeFn H, edgeFn H, edgeFn_involutive H, edgeFn_involutive H⟩

def nodePerm (H : Hypermap n) : Equiv.Perm (Dart n) :=
  ⟨nodeFn H, fun a ↦ nodeFn H (nodeFn H a), nodeFn_period_three H,
    nodeFn_period_three H⟩

def faceInv (H : Hypermap n) : Dart n → Dart n
  | (.n, x) => (.nf, H.face.symm x)
  | (.en, x) => (.n, x)
  | (.f, x) => (.en, x)
  | (.nf, x) => (.f, x)
  | (.e, x) => (.e, H.edge.symm x)
  | (.fe, x) => (.fe, H.node.symm x)

def facePerm (H : Hypermap n) : Equiv.Perm (Dart n) where
  toFun := faceFn H
  invFun := faceInv H
  left_inv := by rintro ⟨t, x⟩; cases t <;> simp [faceFn, faceInv]
  right_inv := by rintro ⟨t, x⟩; cases t <;> simp [faceFn, faceInv]

@[simp] theorem edgePerm_apply (H : Hypermap n) (a : Dart n) :
    edgePerm H a = edgeFn H a := rfl

@[simp] theorem nodePerm_apply (H : Hypermap n) (a : Dart n) :
    nodePerm H a = nodeFn H a := rfl

@[simp] theorem facePerm_apply (H : Hypermap n) (a : Dart n) :
    facePerm H a = faceFn H a := rfl

theorem triangular (H : Hypermap n) (a : Dart n) :
    nodePerm H (facePerm H (edgePerm H a)) = a := by
  rcases a with ⟨t, x⟩
  cases t <;> simp [edgeFn, nodeFn, faceFn, H.edge_node_face, edge_node_face,
    face_edge_node]

@[simp] theorem card_tag : Fintype.card Tag = 6 := by decide

@[simp] theorem card_dart : Fintype.card (Dart n) = 6 * n := by
  simp [Dart, Fintype.card_prod]

noncomputable def cubeEquiv (n : ℕ) : Dart n ≃ Fin (6 * n) :=
  Fintype.equivFinOfCardEq card_dart

noncomputable def cube (H : Hypermap n) : Hypermap (6 * n) where
  edge := (cubeEquiv n).permCongr (edgePerm H)
  node := (cubeEquiv n).permCongr (nodePerm H)
  face := (cubeEquiv n).permCongr (facePerm H)
  edge_node_face := by
    intro x
    obtain ⟨a, rfl⟩ := (cubeEquiv n).surjective x
    simpa using congrArg (cubeEquiv n) (triangular H a)

def Link (H : Hypermap n) (a b : Dart n) : Prop :=
  edgePerm H a = b ∨ nodePerm H a = b ∨ facePerm H a = b

def SameComponent (H : Hypermap n) : Dart n → Dart n → Prop :=
  Relation.EqvGen (Link H)

noncomputable def componentCount (H : Hypermap n) : ℕ :=
  Nat.card (Quotient (Relation.EqvGen.setoid (Link H)))

def Coloring {α : Type*} (H : Hypermap n) (color : Dart n → α) : Prop :=
  (∀ a b, (facePerm H).SameCycle a b → color a = color b) ∧
    (∀ a, color (edgePerm H a) ≠ color a)

def Bridgeless (H : Hypermap n) : Prop :=
  ∀ a, ¬ (facePerm H).SameCycle a (edgePerm H a)

theorem sameCycle_transport {A B : Type*} (q : A ≃ B) (p : Equiv.Perm A) (x y : A) :
    (q.permCongr p).SameCycle (q x) (q y) ↔ p.SameCycle x y := by
  unfold Equiv.Perm.SameCycle
  apply exists_congr
  intro k
  have hpow : (q.permCongr p) ^ k = q.permCongr (p ^ k) :=
    (map_zpow q.permCongrHom p k).symm
  rw [hpow]
  simp

theorem cycleCount_transport {A B : Type*} (q : A ≃ B) (p : Equiv.Perm A) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (q.permCongr p))) =
      Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) := by
  exact (Nat.card_congr (Quotient.congr q
    (fun x y ↦ (sameCycle_transport q p x y).symm))).symm

theorem plain_cube (H : Hypermap n) : (cube H).Plain := by
  intro x
  obtain ⟨a, rfl⟩ := (cubeEquiv n).surjective x
  constructor
  · simpa [cube] using congrArg (cubeEquiv n) (edgeFn_involutive H a)
  · simpa [cube] using (cubeEquiv n).injective.ne (edgeFn_ne H a)

theorem cycleArity_transport {A B : Type*} (q : A ≃ B) (p : Equiv.Perm A) (x : A) :
    Nat.card {y : B // (q.permCongr p).SameCycle (q x) y} =
      Nat.card {y : A // p.SameCycle x y} := by
  exact (Nat.card_congr (q.subtypeEquiv
    (fun y ↦ (sameCycle_transport q p x y).symm))).symm

private theorem eqvGen_map {A B : Type*} {r : A → A → Prop} {s : B → B → Prop}
    (f : A → B) (h : ∀ x y, r x y → Relation.EqvGen s (f x) (f y))
    {x y : A} (hxy : Relation.EqvGen r x y) : Relation.EqvGen s (f x) (f y) := by
  induction hxy with
  | rel a b hab => exact h a b hab
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem sameComponent_transport (H : Hypermap n) (a b : Dart n) :
    (cube H).SameComponent (cubeEquiv n a) (cubeEquiv n b) ↔ SameComponent H a b := by
  constructor
  · intro h
    have h' := eqvGen_map (cubeEquiv n).symm
      (r := (cube H).Link) (s := Link H) ?_ h
    · simpa using h'
    intro x y hxy
    apply Relation.EqvGen.rel
    rcases hxy with he | hn | hf
    · exact Or.inl (by simpa [cube] using congrArg (cubeEquiv n).symm he)
    · exact Or.inr (Or.inl (by simpa [cube] using congrArg (cubeEquiv n).symm hn))
    · exact Or.inr (Or.inr (by simpa [cube] using congrArg (cubeEquiv n).symm hf))
  · apply eqvGen_map (cubeEquiv n)
    intro x y hxy
    apply Relation.EqvGen.rel
    rcases hxy with he | hn | hf
    · exact Or.inl (by simpa [cube] using congrArg (cubeEquiv n) he)
    · exact Or.inr (Or.inl (by simpa [cube] using congrArg (cubeEquiv n) hn))
    · exact Or.inr (Or.inr (by simpa [cube] using congrArg (cubeEquiv n) hf))

theorem componentCount_transport (H : Hypermap n) :
    (cube H).componentCount = componentCount H := by
  exact (Nat.card_congr (Quotient.congr (ra := Relation.EqvGen.setoid (Link H))
    (rb := Relation.EqvGen.setoid (cube H).Link) (cubeEquiv n)
    (fun a b ↦ (sameComponent_transport H a b).symm))).symm

theorem bridgeless_transport (H : Hypermap n) : (cube H).Bridgeless ↔ Bridgeless H := by
  constructor
  · intro h a
    simpa [cube, Hypermap.SameFace, sameCycle_transport] using h (cubeEquiv n a)
  · intro h x
    obtain ⟨a, rfl⟩ := (cubeEquiv n).surjective x
    simpa [cube, Hypermap.SameFace, sameCycle_transport] using h a

theorem coloring_transport {α : Type*} (H : Hypermap n) (color : Fin (6 * n) → α)
    (h : (cube H).Coloring color) : Coloring H (fun a ↦ color (cubeEquiv n a)) := by
  constructor
  · intro a b hab
    apply h.1
    exact (sameCycle_transport (cubeEquiv n) (facePerm H) a b).mpr hab
  · intro a
    simpa [cube] using h.2 (cubeEquiv n a)

end FourColor.Cubification

/-!
Orbit sizes in the sixfold cubification. Source: Gonthier (2005), Section 5.1,
PDF p. 26, cubification paragraph (unnumbered), and pinned Rocq `cube.v`,
`plain_cube`, `cubic_cube`, and `genus_cube`. The finite orbit partition below
is a Lean bridge used to express the source's edge and node counts.
-/

namespace FourColor.Cubification

open scoped BigOperators

private noncomputable def cycleDarts {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (p.SameCycle x)

private theorem mem_cycleDarts {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x y : α) : y ∈ cycleDarts p x ↔ p.SameCycle x y := by
  classical
  simp [cycleDarts]

private noncomputable def cycleFiber {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (q : Quotient (Equiv.Perm.SameCycle.setoid p)) : Finset α := by
  classical
  exact Finset.univ.filter (fun y ↦ Quotient.mk _ y = q)

private theorem quotient_fiber {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) :
    cycleFiber p (Quotient.mk _ x) = cycleDarts p x := by
  classical
  ext y
  simp only [cycleFiber, Finset.mem_filter, Finset.mem_univ, true_and, mem_cycleDarts,
    Quotient.eq_iff_equiv]
  exact Equiv.Perm.sameCycle_comm

private theorem card_eq_cycle_count_mul {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (k : ℕ) (hk : ∀ x, (cycleDarts p x).card = k) :
    Nat.card α = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid p)) * k := by
  classical
  letI := Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset α))
    (t := (Finset.univ : Finset (Quotient (Equiv.Perm.SameCycle.setoid p))))
    (f := Quotient.mk (Equiv.Perm.SameCycle.setoid p)) (fun _ _ ↦ Finset.mem_univ _)
  have hterm : ∀ q : Quotient (Equiv.Perm.SameCycle.setoid p), (cycleFiber p q).card = k := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => rw [quotient_fiber, hk]
  change (Finset.univ : Finset α).card = ∑ q, (cycleFiber p q).card at hcard
  simp_rw [hterm] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard

private theorem cycleDarts_card_two {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) (h2 : p (p x) = x) (h1 : p x ≠ x) :
    (cycleDarts p x).card = 2 := by
  classical
  have hcycle : ∀ y, p.SameCycle x y ↔ y = x ∨ y = p x := by
    intro y
    constructor
    · intro hxy
      obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
      clear hxy
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · exact Or.inr (congrArg p h)
        · exact Or.inl ((congrArg p h).trans h2)
    · rintro (rfl | rfl)
      · exact .refl _ _
      · exact ⟨1, by simp⟩
  have hdarts : cycleDarts p x = {x, p x} := by
    ext y
    simp [mem_cycleDarts, hcycle]
  rw [hdarts, Finset.card_pair]
  exact h1.symm

private theorem cycleDarts_card_three {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) (h3 : p (p (p x)) = x)
    (h1 : p x ≠ x) (h2 : p (p x) ≠ x) : (cycleDarts p x).card = 3 := by
  classical
  have hcycle : ∀ y, p.SameCycle x y ↔ y = x ∨ y = p x ∨ y = p (p x) := by
    intro y
    constructor
    · intro hxy
      obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
      clear hxy
      induction k with
      | zero => exact Or.inl rfl
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h | h
        · exact Or.inr (Or.inl (congrArg p h))
        · exact Or.inr (Or.inr (congrArg p h))
        · exact Or.inl ((congrArg p h).trans h3)
    · rintro (rfl | rfl | rfl)
      · exact .refl _ _
      · exact ⟨1, by simp⟩
      · exact (Equiv.Perm.SameCycle.refl p x).apply_right.apply_right
  have hdarts : cycleDarts p x = {x, p x, p (p x)} := by
    ext y
    simp [mem_cycleDarts, hcycle]
  have hpair : p x ≠ p (p x) := fun h ↦ h1 (p.injective h).symm
  rw [hdarts, Finset.card_insert_of_notMem]
  · rw [Finset.card_pair hpair]
  · simp [h1.symm, h2.symm]

private theorem cycle_subtype_card {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (x : α) :
    Nat.card {y : α // p.SameCycle x y} = (cycleDarts p x).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1

private theorem edge_darts_card {n : ℕ} (H : Hypermap n) (a : Dart n) :
    (cycleDarts (edgePerm H) a).card = 2 := by
  apply cycleDarts_card_two
  · simpa only [edgePerm_apply] using edgeFn_involutive H a
  · simpa only [edgePerm_apply] using edgeFn_ne H a

private theorem node_darts_card {n : ℕ} (H : Hypermap n) (a : Dart n) :
    (cycleDarts (nodePerm H) a).card = 3 := by
  apply cycleDarts_card_three
  · simpa only [nodePerm_apply] using nodeFn_period_three H a
  · simpa only [nodePerm_apply] using nodeFn_ne H a
  · simpa only [nodePerm_apply] using nodeFn_two_ne H a

theorem edge_cycle_card {n : ℕ} (H : Hypermap n) (a : Dart n) :
    Nat.card {b : Dart n // (edgePerm H).SameCycle a b} = 2 := by
  rw [cycle_subtype_card, edge_darts_card]

theorem node_cycle_card {n : ℕ} (H : Hypermap n) (a : Dart n) :
    Nat.card {b : Dart n // (nodePerm H).SameCycle a b} = 3 := by
  rw [cycle_subtype_card, node_darts_card]

theorem edge_count {n : ℕ} (H : Hypermap n) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (edgePerm H))) = 3 * n := by
  have h := card_eq_cycle_count_mul (edgePerm H) 2 (edge_darts_card H)
  rw [Nat.card_eq_fintype_card, card_dart] at h
  omega

theorem node_count {n : ℕ} (H : Hypermap n) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (nodePerm H))) = 2 * n := by
  have h := card_eq_cycle_count_mul (nodePerm H) 3 (node_darts_card H)
  rw [Nat.card_eq_fintype_card, card_dart] at h
  omega

theorem edgeCount_cube {n : ℕ} (H : Hypermap n) : (cube H).edgeCount = 3 * n := by
  rw [Hypermap.edgeCount, cube, cycleCount_transport, edge_count]

theorem nodeCount_cube {n : ℕ} (H : Hypermap n) : (cube H).nodeCount = 2 * n := by
  rw [Hypermap.nodeCount, cube, cycleCount_transport, node_count]

theorem cubic_cube {n : ℕ} (H : Hypermap n) : (cube H).Cubic := by
  intro x
  obtain ⟨a, rfl⟩ := (cubeEquiv n).surjective x
  change Nat.card {b : Fin (6 * n) //
    ((cubeEquiv n).permCongr (nodePerm H)).SameCycle (cubeEquiv n a) b} = 3
  rw [cycleArity_transport, node_cycle_card]

end FourColor.Cubification

/-!
# Connected components of the sixfold cubification

The projection and tag inclusion below formalize the component adjunction in
`genus_cube` of the pinned Rocq `cube.v`. Source: Gonthier (2005), Section 5.1,
PDF p. 26, unnumbered cubification paragraph; Section 3, PDF p. 6, cubic reduction.
Every tag over a dart is connected to its `n` tag, so this argument also covers
the empty and disconnected hypermaps without additional hypotheses.
-/

namespace FourColor.Cubification

variable {n : ℕ} (H : Hypermap n)

private theorem edge_step (a : Dart n) : SameComponent H a (edgeFn H a) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

private theorem node_step (a : Dart n) : SameComponent H a (nodeFn H a) :=
  Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl))

private theorem face_step (a : Dart n) : SameComponent H a (faceFn H a) :=
  Relation.EqvGen.rel _ _ (Or.inr (Or.inr rfl))

theorem tag_sameComponent_n (t : Tag) (x : Fin n) :
    SameComponent H (t, x) (Tag.n, x) := by
  have hnen : SameComponent H (Tag.n, x) (Tag.en, x) := face_step H (Tag.n, x)
  have henf : SameComponent H (Tag.en, x) (Tag.f, x) := face_step H (Tag.en, x)
  have hfnf : SameComponent H (Tag.f, x) (Tag.nf, x) := face_step H (Tag.f, x)
  have hnf := Relation.EqvGen.trans _ _ _ hnen henf
  have hnnf := Relation.EqvGen.trans _ _ _ hnf hfnf
  cases t with
  | n => exact Relation.EqvGen.refl _
  | en => exact Relation.EqvGen.symm _ _ hnen
  | f => exact Relation.EqvGen.symm _ _ hnf
  | nf => exact Relation.EqvGen.symm _ _ hnnf
  | e =>
      exact Relation.EqvGen.trans _ _ _ (node_step H (Tag.e, x))
        (Relation.EqvGen.symm _ _ hnf)
  | fe => exact Relation.EqvGen.symm _ _ (edge_step H (Tag.n, x))

private theorem original_edge_step (x : Fin n) : H.SameComponent x (H.edge x) :=
  Relation.EqvGen.rel _ _ (Or.inl rfl)

private theorem original_node_step (x : Fin n) : H.SameComponent x (H.node x) :=
  Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl))

private theorem original_face_step (x : Fin n) : H.SameComponent x (H.face x) :=
  Relation.EqvGen.rel _ _ (Or.inr (Or.inr rfl))

private theorem project_edge_step (a : Dart n) :
    H.SameComponent a.2 (edgeFn H a).2 := by
  rcases a with ⟨t, x⟩
  have hnf : H.SameComponent x (H.node (H.face x)) :=
    Relation.EqvGen.trans _ _ _ (original_face_step H x)
      (original_node_step H (H.face x))
  cases t with
  | n => exact Relation.EqvGen.refl _
  | en => exact original_edge_step H x
  | f => exact hnf
  | nf => exact hnf
  | e => exact original_edge_step H x
  | fe => exact Relation.EqvGen.refl _

private theorem project_node_step (a : Dart n) :
    H.SameComponent a.2 (nodeFn H a).2 := by
  rcases a with ⟨t, x⟩
  have hnf : H.SameComponent x (H.node (H.face x)) :=
    Relation.EqvGen.trans _ _ _ (original_face_step H x)
      (original_node_step H (H.face x))
  have hfe : H.SameComponent x (H.face (H.edge x)) :=
    Relation.EqvGen.trans _ _ _ (original_edge_step H x)
      (original_face_step H (H.edge x))
  cases t with
  | n => exact original_node_step H x
  | en => exact Relation.EqvGen.refl _
  | f => exact original_edge_step H x
  | nf => exact hnf
  | e => exact Relation.EqvGen.refl _
  | fe => exact hfe

private theorem project_face_step (a : Dart n) :
    H.SameComponent a.2 (faceFn H a).2 := by
  rcases a with ⟨t, x⟩
  cases t with
  | n => exact Relation.EqvGen.refl _
  | en => exact Relation.EqvGen.refl _
  | f => exact Relation.EqvGen.refl _
  | nf => exact original_face_step H x
  | e => exact original_edge_step H x
  | fe => exact original_node_step H x

theorem sameComponent_project {a b : Dart n} (h : SameComponent H a b) :
    H.SameComponent a.2 b.2 := by
  induction h with
  | rel a b hab =>
      rcases hab with he | hn | hf
      · rw [← he]
        exact project_edge_step H a
      · rw [← hn]
        exact project_node_step H a
      · rw [← hf]
        exact project_face_step H a
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

private theorem n_step_of_tag_step {t s : Tag} {x y : Fin n}
    (h : SameComponent H (t, x) (s, y)) : SameComponent H (Tag.n, x) (Tag.n, y) :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (tag_sameComponent_n H t x))
    (Relation.EqvGen.trans _ _ _ h (tag_sameComponent_n H s y))

theorem sameComponent_include {x y : Fin n} (h : H.SameComponent x y) :
    SameComponent H (Tag.n, x) (Tag.n, y) := by
  induction h with
  | rel x y hxy =>
      rcases hxy with he | hn | hf
      · subst y
        exact n_step_of_tag_step H (t := Tag.e) (s := Tag.e) (face_step H (Tag.e, x))
      · subst y
        exact n_step_of_tag_step H (t := Tag.fe) (s := Tag.fe) (face_step H (Tag.fe, x))
      · subst y
        exact n_step_of_tag_step H (t := Tag.nf) (s := Tag.n) (face_step H (Tag.nf, x))
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

theorem sameComponent_iff (a b : Dart n) :
    SameComponent H a b ↔ H.SameComponent a.2 b.2 := by
  constructor
  · exact sameComponent_project H
  · intro h
    exact Relation.EqvGen.trans _ _ _ (tag_sameComponent_n H a.1 a.2)
      (Relation.EqvGen.trans _ _ _ (sameComponent_include H h)
        (Relation.EqvGen.symm _ _ (tag_sameComponent_n H b.1 b.2)))

def componentEquiv :
    Quotient (Relation.EqvGen.setoid (Link H)) ≃
      Quotient (Relation.EqvGen.setoid H.Link) where
  toFun := Quotient.map' Prod.snd (fun _ _ h ↦ sameComponent_project H h)
  invFun := Quotient.map' (fun x ↦ (Tag.n, x)) (fun _ _ h ↦ sameComponent_include H h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ a =>
        exact Quotient.sound (Relation.EqvGen.symm _ _ (tag_sameComponent_n H a.1 a.2))
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => rfl

theorem componentCount_eq : componentCount H = H.componentCount :=
  Nat.card_congr (componentEquiv H)

end FourColor.Cubification

/-!
# Face cycles and coloring transport for sixfold cubification

Source: Gonthier (2005), Section 5.1, PDF p. 26, unnumbered cubification paragraph;
pinned Rocq `cube.v`, lines 44–81, 101–188 and 190–207, at commit
`c1d6b1cd5288bea4b067aac13cdde3c18dffe018`. This module proves the raw
permutation facts used by the unchanged cubic-normalization target.

Mathlib search found `SameCycle.exists_nat_pow_eq` and the permutation-power API;
the two generic helpers below supply the remaining finite mapped-cycle arguments.
-/

namespace FourColor.Cubification

private theorem perm_pow_map {A B : Type*} (p : Equiv.Perm A) (q : Equiv.Perm B)
    (i : A → B) (hi : ∀ x, q (i x) = i (p x)) (k : ℕ) (x : A) :
    (q ^ k) (i x) = i ((p ^ k) x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, hi, pow_succ', Equiv.Perm.mul_apply]

theorem sameCycle_map {A B : Type*} [Finite A] (p : Equiv.Perm A) (q : Equiv.Perm B)
    (i : A → B) (hi : ∀ x, q (i x) = i (p x)) {x y : A}
    (h : p.SameCycle x y) : q.SameCycle (i x) (i y) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast, perm_pow_map p q i hi, hk]

theorem sameCycle_invariant {A B : Type*} [Finite A] (p : Equiv.Perm A) (i : A → B)
    (hi : ∀ x, i (p x) = i x) {x y : A} (h : p.SameCycle x y) : i x = i y := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hp : ∀ (k : ℕ) (x : A), i ((p ^ k) x) = i x := by
    intro k x
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hi, ih]
  exact (hp k x).symm.trans (congrArg i hk)

variable {n : ℕ}

abbrev FaceKeyType (H : Hypermap n) :=
  Quotient (Equiv.Perm.SameCycle.setoid H.edge) ⊕
    Quotient (Equiv.Perm.SameCycle.setoid H.node) ⊕
      Quotient (Equiv.Perm.SameCycle.setoid H.face)

/-- Cubification has one face for each original edge, node, or face orbit. -/
def faceKey (H : Hypermap n) : Dart n → FaceKeyType H
  | (.e, x) => Sum.inl (Quotient.mk _ x)
  | (.fe, x) => Sum.inr (Sum.inl (Quotient.mk _ x))
  | (_, x) => Sum.inr (Sum.inr (Quotient.mk _ x))

theorem faceKey_face (H : Hypermap n) (a : Dart n) :
    faceKey H (facePerm H a) = faceKey H a := by
  rcases a with ⟨t, x⟩
  cases t <;> simp only [facePerm_apply, faceFn, faceKey]
  · exact congrArg (fun q ↦ Sum.inr (Sum.inr q))
      (Quotient.sound (Equiv.Perm.SameCycle.refl H.face x).apply_left)
  · exact congrArg Sum.inl
      (Quotient.sound (Equiv.Perm.SameCycle.refl H.edge x).apply_left)
  · exact congrArg (fun q ↦ Sum.inr (Sum.inl q))
      (Quotient.sound (Equiv.Perm.SameCycle.refl H.node x).apply_left)

theorem faceKey_eq_of_sameCycle (H : Hypermap n) {a b : Dart n}
    (h : (facePerm H).SameCycle a b) : faceKey H a = faceKey H b :=
  sameCycle_invariant (facePerm H) (faceKey H) (faceKey_face H) h

theorem sameCycle_e (H : Hypermap n) {x y : Fin n} (h : H.edge.SameCycle x y) :
    (facePerm H).SameCycle (.e, x) (.e, y) :=
  sameCycle_map H.edge (facePerm H) (fun x ↦ (.e, x)) (fun _ ↦ rfl) h

theorem sameCycle_fe (H : Hypermap n) {x y : Fin n} (h : H.node.SameCycle x y) :
    (facePerm H).SameCycle (.fe, x) (.fe, y) :=
  sameCycle_map H.node (facePerm H) (fun x ↦ (.fe, x)) (fun _ ↦ rfl) h

theorem facePerm_four_nf (H : Hypermap n) (x : Fin n) :
    (facePerm H ^ 4) (.nf, x) = (.nf, H.face x) := by
  norm_num [pow_succ, Equiv.Perm.mul_apply, facePerm_apply, faceFn]

theorem sameCycle_nf (H : Hypermap n) {x y : Fin n} (h : H.face.SameCycle x y) :
    (facePerm H).SameCycle (.nf, x) (.nf, y) :=
  (sameCycle_map H.face (facePerm H ^ 4) (fun x ↦ (.nf, x))
    (facePerm_four_nf H) h).of_pow

theorem sameCycle_to_nf (H : Hypermap n) (a : Dart n)
    (he : a.1 ≠ .e) (hn : a.1 ≠ .fe) : (facePerm H).SameCycle a (.nf, a.2) := by
  rcases a with ⟨t, x⟩
  cases t
  · refine ⟨((3 : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast]
    norm_num [pow_succ, Equiv.Perm.mul_apply, facePerm_apply, faceFn]
  · refine ⟨((2 : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast]
    norm_num [pow_succ, Equiv.Perm.mul_apply, facePerm_apply, faceFn]
  · refine ⟨1, ?_⟩
    simp [facePerm_apply, faceFn]
  · exact Equiv.Perm.SameCycle.rfl
  · exact (he rfl).elim
  · exact (hn rfl).elim

theorem sameCycle_of_faceKey_eq (H : Hypermap n) {a b : Dart n}
    (h : faceKey H a = faceKey H b) : (facePerm H).SameCycle a b := by
  rcases a with ⟨t, x⟩
  rcases b with ⟨s, y⟩
  cases t <;> cases s <;>
    simp only [faceKey, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl] at h
  all_goals first
    | exact sameCycle_e H (Quotient.exact h)
    | exact sameCycle_fe H (Quotient.exact h)
    | apply (sameCycle_to_nf H _ (by simp) (by simp)).trans
      apply (sameCycle_nf H (Quotient.exact h)).trans
      apply Equiv.Perm.SameCycle.symm
      apply sameCycle_to_nf H <;> simp

theorem sameCycle_faceKey_iff (H : Hypermap n) (a b : Dart n) :
    (facePerm H).SameCycle a b ↔ faceKey H a = faceKey H b :=
  ⟨faceKey_eq_of_sameCycle H, sameCycle_of_faceKey_eq H⟩

theorem faceKey_surjective (H : Hypermap n) : Function.Surjective (faceKey H) := by
  intro q
  rcases q with q | q
  · induction q using Quotient.inductionOn with
    | h x => exact ⟨(.e, x), rfl⟩
  · rcases q with q | q
    · induction q using Quotient.inductionOn with
      | h x => exact ⟨(.fe, x), rfl⟩
    · induction q using Quotient.inductionOn with
      | h x => exact ⟨(.nf, x), rfl⟩

noncomputable def faceCycleEquiv (H : Hypermap n) :
    Quotient (Equiv.Perm.SameCycle.setoid (facePerm H)) ≃ FaceKeyType H :=
  Equiv.ofBijective
    (Quotient.lift (faceKey H) (fun _ _ h ↦ faceKey_eq_of_sameCycle H h)) (by
      constructor
      · intro a b hab
        induction a, b using Quotient.inductionOn₂ with
        | h a b => exact Quotient.sound (sameCycle_of_faceKey_eq H hab)
      · intro q
        obtain ⟨a, ha⟩ := faceKey_surjective H q
        exact ⟨Quotient.mk _ a, ha⟩)

theorem face_count (H : Hypermap n) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (facePerm H))) =
      H.edgeCount + H.nodeCount + H.faceCount := by
  rw [Nat.card_congr (faceCycleEquiv H)]
  simp only [FaceKeyType, Nat.card_sum, Hypermap.edgeCount, Hypermap.nodeCount,
    Hypermap.faceCount, Nat.add_assoc]

theorem bridgeless_iff (H : Hypermap n) : Bridgeless H ↔ H.Bridgeless := by
  constructor
  · intro h x hsame
    apply h (.en, x)
    apply sameCycle_of_faceKey_eq H
    exact congrArg (fun q ↦ Sum.inr (Sum.inr q)) (Quotient.sound hsame)
  · intro h a hsame
    have hkey := faceKey_eq_of_sameCycle H hsame
    rcases a with ⟨t, x⟩
    cases t <;>
      simp only [edgePerm_apply, edgeFn, faceKey, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl] at hkey
    · exact h x (Quotient.exact hkey)
    · have hnf : H.node (H.face x) = H.edge.symm x := by
        simpa using H.edge_node_face (H.edge.symm x)
      apply h (H.edge.symm x)
      simpa [Hypermap.SameFace, hnf] using (Quotient.exact hkey).symm

theorem coloring_transfer (H : Hypermap n) {α : Type*} {color : Dart n → α}
    (h : Coloring H color) : H.Coloring (fun x ↦ color (.nf, x)) := by
  constructor
  · intro x y hsame
    exact h.1 _ _ (sameCycle_nf H hsame)
  · intro x
    have hedge := h.2 (.en, x)
    change color (.nf, H.edge x) ≠ color (.en, x) at hedge
    rw [h.1 (.en, x) (.nf, x) (sameCycle_to_nf H _ (by simp) (by simp))] at hedge
    exact hedge

end FourColor.Cubification

/-!
# Preservation properties of sixfold cubification

Source: pinned Rocq `cube.v`, `genus_cube`, `planar_cube`, `bridgeless_cube`,
and `cube_colorable`; Gonthier (2005), Section 3, PDF p. 6, item a).
The exact Euler equality is proved from orbit and component counts.
-/

namespace FourColor.Cubification

variable {n : ℕ}

theorem faceCount_cube (H : Hypermap n) :
    (cube H).faceCount = H.edgeCount + H.nodeCount + H.faceCount := by
  rw [Hypermap.faceCount, cube, cycleCount_transport, face_count]

theorem componentCount_cube (H : Hypermap n) : (cube H).componentCount = H.componentCount := by
  rw [componentCount_transport, componentCount_eq]

theorem planar_cube (H : Hypermap n) : (cube H).Planar ↔ H.Planar := by
  unfold Hypermap.Planar
  rw [edgeCount_cube, nodeCount_cube, faceCount_cube, componentCount_cube]
  omega

theorem bridgeless_cube (H : Hypermap n) : (cube H).Bridgeless ↔ H.Bridgeless :=
  (bridgeless_transport H).trans (bridgeless_iff H)

theorem cube_colorable (H : Hypermap n) : (cube H).FourColorable → H.FourColorable := by
  rintro ⟨color, hcolor⟩
  exact ⟨fun x ↦ color (cubeEquiv n (.nf, x)),
    coloring_transfer H (coloring_transport H color hcolor)⟩

end FourColor.Cubification

open FourColor

theorem solution :
    ∀ (n : ℕ) (H : Hypermap n), ∃ K : Hypermap (6 * n),
      K.Plain ∧ K.Cubic ∧ (K.Planar ↔ H.Planar) ∧
        (K.Bridgeless ↔ H.Bridgeless) ∧ (K.FourColorable → H.FourColorable) := by
  intro n H
  exact ⟨Cubification.cube H, Cubification.plain_cube H, Cubification.cubic_cube H,
    Cubification.planar_cube H, Cubification.bridgeless_cube H,
    Cubification.cube_colorable H⟩
