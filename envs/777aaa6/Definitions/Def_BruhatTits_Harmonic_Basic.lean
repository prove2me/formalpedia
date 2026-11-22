-- Prove2me | Definitions.Def_BruhatTits_Harmonic_Basic
-- name    : BruhatTits_Harmonic_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:41:29.887342+00:00
-- url     : https://prove2.me/theorems/597188c0-2763-4609-a166-284073b9cca4
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Harmonic/Basic.lean

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
namespace SimpleGraph
section
variable {X : SimpleGraph V}
def incidenceEquiv (v : V) : { e : X.edgeSet | v ∈ e.val } ≃ X.incidenceSet v where
  toFun e := ⟨e.val.val, ⟨e.val.property, e.property⟩⟩
  invFun e := ⟨⟨e.val, e.property.left⟩, e.property.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance (v : V) [Fintype (X.neighborSet v)] : Finite { e : X.edgeSet | v ∈ e.val } :=
  Finite.of_equiv _ (incidenceEquiv v).symm
def incidenceFinset' (v : V) [Fintype (X.neighborSet v)] : Finset X.edgeSet :=
  let s : Set X.edgeSet := { e | v ∈ e.val }
  have hs : s.Finite := by
    show Finite s
    infer_instance
  hs.toFinset
lemma mem_incidenceFinset' (v : V) [Fintype (X.neighborSet v)] (e : X.edgeSet) :
    e ∈ incidenceFinset' v ↔ v ∈ e.val := by
  simp [incidenceFinset']
def laplace [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : X.edgeSet → M) (v : V) : M :=
  w v • ∑ e ∈ X.incidenceFinset' v, f e
def IsHarmonic [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : X.edgeSet → M) : Prop :=
  X.laplace w f = 0
end
section Surjectivity
structure Tree (V : Type*) extends SimpleGraph V where
  isTree : IsTree toSimpleGraph
namespace Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)
section API
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma exists_path_eq_append_of_isPath_of_mem_support {v w x : V} (p : X.Walk v w) (hp : p.IsPath)
    (hx : x ∈ p.support) :
    ∃ (r : X.Walk v x) (s : X.Walk x w), r.IsPath ∧ s.IsPath ∧ p = r.append s := by
  rw [p.mem_support_iff_exists_append] at hx
  obtain ⟨r, s, hrs⟩ := hx
  have : (r.append s).IsPath := by rwa [← hrs]
  refine ⟨r, s, ?_, ?_, hrs⟩
  apply Walk.IsPath.of_append_left this
  apply Walk.IsPath.of_append_right this
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma exists_path_eq_cons_of_isPath_of_mem_support {v w : V} (h : X.Adj w v) (p : X.Walk w v₀)
    (hv : v ∈ p.support) (hpath : p.IsPath) : ∃ (r : X.Walk v v₀), r.IsPath ∧ p = r.cons h := by
  obtain ⟨r, s, hr, hs, hrs⟩ := exists_path_eq_append_of_isPath_of_mem_support p hpath hv
  let r' : X.Walk w v := h.toWalk
  have hr' : r'.IsPath := by simpa [r'] using h.ne
  let pr' : X.Path w v := ⟨r', hr'⟩
  let pr : X.Path w v := ⟨r, hr⟩
  have : pr = pr' := X.isTree.IsAcyclic.path_unique _ _
  have hrr' : r = r' := by rwa [Subtype.ext_iff] at this
  use s, hs
  rw [hrs, hrr']
  simp [r']
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma dist_ne_of_of_adj {v w : V} (h : X.Adj v w) : X.dist v₀ v ≠ X.dist v₀ w := by
  obtain ⟨pv, hpvpath, hpvlength⟩ := X.isTree.isConnected.exists_path_of_dist v v₀
  obtain ⟨pw, hpwpath, hpwlength⟩ := X.isTree.isConnected.exists_path_of_dist w v₀
  let q : X.Walk v v₀ := pw.cons' _ _ _ h
  intro hdist
  let pv' : X.Path v v₀ := ⟨pv, hpvpath⟩
  have hlen : pv.length = pw.length := by
    rw [hpvlength, dist_comm, hdist, dist_comm, ← hpwlength]
  have hqpath : q.IsPath := by
    simp only [Walk.cons_isPath_iff, hpwpath, true_and, q]
    intro hc
    obtain ⟨r, hr, hpr⟩ := X.exists_path_eq_cons_of_isPath_of_mem_support v₀ h.symm pw hc hpwpath
    let r' : X.Path v v₀ := ⟨r, hr⟩
    have : pv' = r' := X.isTree.IsAcyclic.path_unique _ _
    have : pv = r := by rwa [Subtype.ext_iff] at this
    have : pw.length = pv.length + 1 := by simp [this, hpr]
    omega
  let q' : X.Path v v₀ := ⟨q, hqpath⟩
  have : pv' = q' := X.isTree.IsAcyclic.path_unique _ _
  have heq : pv = q := by
    show pv'.val = q'.val
    rwa [← Subtype.ext_iff]
  have : q.length = pw.length + 1 := by simp [q]
  rw [← heq, hpvlength, dist_comm, hdist, dist_comm, ← hpwlength] at this
  omega
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma exists_ordered (e : X.edgeSet) :
    ∃ p : V × V, X.dist v₀ p.1 < X.dist v₀ p.2 ∧ Sym2.mk p.1 p.2 = e := by
  obtain ⟨p, hp⟩ := Quot.exists_rep e.val
  if h : X.dist v₀ p.1 < X.dist v₀ p.2
  then use p
  else
    use (p.2, p.1)
    simp only
    constructor
    · by_contra hc
      have hdist : X.dist v₀ p.1 = X.dist v₀ p.2 := by omega
      have hadj : s(p.1, p.2) ∈ X.edgeSet := by
        show Quot.mk (Sym2.Rel V) p ∈ _
        rw [hp]
        exact e.property
      rw [mem_edgeSet] at hadj
      apply dist_ne_of_of_adj v₀ hadj hdist
    · rw [Sym2.eq_swap]
      exact hp
def source (e : X.edgeSet) : V :=
  (X.exists_ordered v₀ e).choose.1
def target (e : X.edgeSet) : V :=
  (X.exists_ordered v₀ e).choose.2
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma norm_source_lt_norm_target (e : X.edgeSet) :
    X.dist v₀ (X.source v₀ e) < X.dist v₀ (X.target v₀ e) :=
  (X.exists_ordered v₀ e).choose_spec.left
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma edge_eq_mk_source_target (e : X.edgeSet) :
    e.val = s(source v₀ e, target v₀ e) :=
  (exists_ordered v₀ e).choose_spec.right.symm
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma source_mem (e : X.edgeSet) : X.source v₀ e ∈ e.val := by
  simp [edge_eq_mk_source_target v₀]
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma target_mem (e : X.edgeSet) : X.target v₀ e ∈ e.val := by
  simp [edge_eq_mk_source_target v₀]
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma source_adj_target (e : X.edgeSet) :
    X.Adj (X.source v₀ e) (X.target v₀ e) := by
  rw [adj_iff_exists_edge]
  refine ⟨?_, ?_⟩
  · intro hc
    have := norm_source_lt_norm_target v₀ e
    simp [hc] at this
  · exact ⟨e, e.property, source_mem v₀ e, target_mem v₀ e⟩
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma norm_target_eq_norm_source_add_one (e : X.edgeSet) :
    X.dist v₀ (X.target v₀ e) = X.dist v₀ (X.source v₀ e) + 1 := by
  apply le_antisymm
  · have h := X.source_adj_target v₀ e
    rw [← dist_eq_one_iff_adj] at h
    rw [← h]
    apply X.isTree.isConnected.dist_triangle
  · have := norm_source_lt_norm_target v₀ e
    omega
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma eq_source_or_eq_target_of_mem (e : X.edgeSet) (v : V) (hv : v ∈ e.val) :
    X.source v₀ e = v ∨ X.target v₀ e = v := by
  rw [edge_eq_mk_source_target v₀, Sym2.mem_iff] at hv
  tauto
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
lemma zero_lt_norm_target (e : X.edgeSet) : 0 < X.dist v₀ (X.target v₀ e) := by
  rw [norm_target_eq_norm_source_add_one]
  omega
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma source_eq_origin_of_mem (e : X.edgeSet) (h : v₀ ∈ e.val) :
    X.source v₀ e = v₀ := by
  rcases eq_source_or_eq_target_of_mem v₀ e v₀ h with hm | hm
  · exact hm
  · have : 0 < X.dist v₀ v₀ := by
      nth_rw 2 [← hm]
      exact zero_lt_norm_target v₀ e
    simp [dist_self] at this
def outwardCone (w : V) : Finset V :=
  let s : Set V := { v : V | X.Adj w v ∧ X.dist v₀ w < X.dist v₀ v }
  have hs : s.Finite := by
    apply Set.Finite.subset
    · exact Set.toFinite (X.neighborSet w)
    · intro a ha
      exact ha.left
  hs.toFinset
def outwardEdgeCone (w : V) : Finset X.edgeSet :=
  let s : Set X.edgeSet :=
    { e | w ∈ e.val ∧ X.source v₀ e = w }
  have hs : s.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (incidenceFinset' w))
    intro e he
    simp only [Finset.mem_coe, mem_incidenceFinset']
    exact he.left
  hs.toFinset
lemma mem_outwardEdgeCone_iff (w : V) (e : X.edgeSet) :
    e ∈ X.outwardEdgeCone v₀ w ↔ w ∈ e.val ∧ X.source v₀ e = w := by
  simp [outwardEdgeCone]
lemma outwardEdgeCone_nonempty_of_source (e : X.edgeSet) :
    (X.outwardEdgeCone v₀ (X.source v₀ e)).Nonempty := by
  use e
  rw [mem_outwardEdgeCone_iff]
  simp
def distinguishedEdge (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) : X.edgeSet :=
  hw.choose
lemma distinguishedEdge_mem (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) :
    X.distinguishedEdge v₀ w hw ∈ X.outwardEdgeCone v₀ w :=
  hw.choose_spec
@[simp]
lemma source_distinguishedEdge (v : V) (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    X.source v₀ (distinguishedEdge v₀ v hnonempty) = v := by
  have := distinguishedEdge_mem v₀ v hnonempty
  rw [mem_outwardEdgeCone_iff] at this
  exact this.right
omit [(v : V) → Fintype (X.neighborSet v)] in
/-- For every vertex `w` different from the root vertex `v₀` there exists an edge `e`, whose
target is `w`. -/
lemma exists_edge_dist_source_lt (w : V) (hw : 0 < X.dist v₀ w) :
    ∃ (e : X.edgeSet), X.target v₀ e = w := by
  obtain ⟨p, hp, hplen⟩ := X.isTree.isConnected.exists_path_of_dist w v₀
  induction p using Walk.rec with
  | nil =>
    simp_rw [Walk.length_nil] at hplen
    omega
  | @cons x y z hadj p ih =>
    rw [adj_iff_exists_edge_coe] at hadj
    obtain ⟨e, he⟩ := hadj
    use e
    have hx : x ∈ e.val := by simp [he]
    have hy : y ∈ e.val := by simp [he]
    have hp' : p.IsPath := by
      simp only [Walk.cons_isPath_iff] at hp
      exact hp.left
    obtain ⟨q, hq, hqlen⟩ := X.isTree.isConnected.exists_path_of_dist y z
    let p' : X.Path y z := ⟨p, hp'⟩
    let q' : X.Path y z := ⟨q, hq⟩
    have : p' = q' := X.isTree.IsAcyclic.path_unique _ _
    have hpq : p = q := by rwa [Subtype.ext_iff] at this
    have hdist : X.dist z y < X.dist z x := by
      rw [dist_comm, ← hqlen, ← hpq, dist_comm, ← hplen]
      simp
    rcases eq_source_or_eq_target_of_mem z e x hx with hsource | h
    · have hsec : target z e = y := by
        rcases eq_source_or_eq_target_of_mem z e y hy with h' | h'
        · rw [h'] at hsource
          absurd hsource.symm
          exact hadj.ne
        · assumption
      rw [← hsource, ← hsec, norm_target_eq_norm_source_add_one] at hdist
      omega
    · assumption
def edgeTowardsOrigin (w : V) (hw : 0 < X.dist v₀ w) : X.edgeSet :=
  (X.exists_edge_dist_source_lt v₀ w hw).choose
omit [(v : V) → Fintype (X.neighborSet v)] in
@[simp]
lemma edgeTowardsOrigin_target_eq (w : V) (hw : 0 < X.dist v₀ w) :
    X.target v₀ (X.edgeTowardsOrigin v₀ w hw) = w :=
  (X.exists_edge_dist_source_lt v₀ w hw).choose_spec
end API
section Construction
variable (n : ℕ) (g : X.edgeSet → M)
def auxBorder (e : X.edgeSet) (he : X.dist v₀ (X.target v₀ e) = n + 1) : M :=
  match n with
  | 0 =>
    let d : V := X.source v₀ e
    have hd : (X.outwardEdgeCone v₀ d).Nonempty := by
      use e
      rw [mem_outwardEdgeCone_iff]
      simp only [d, and_true]
      exact source_mem v₀ e
    if X.distinguishedEdge v₀ d hd = e
      then (w d)⁻¹ • f d
      else 0
  | n + 1 =>
    let d : V := X.source v₀ e
    have hd : (X.outwardEdgeCone v₀ d).Nonempty := by
      use e
      rw [mem_outwardEdgeCone_iff]
      simp only [d, and_true]
      exact source_mem v₀ e
    have hd2 : 0 < X.dist v₀ d := by
      rw [norm_target_eq_norm_source_add_one] at he
      rw [add_left_inj] at he
      simp_rw [d]
      omega
    let q : X.edgeSet := X.edgeTowardsOrigin v₀ d hd2
    if X.distinguishedEdge v₀ d hd = e
      then (w d)⁻¹ • f d - g q
      else 0
def aux (n : ℕ) : X.edgeSet → M := match n with
  /- arbitrary value in step zero. -/
  | 0 => fun _ ↦ 0
  | n + 1 => fun e ↦
      /- if the norm of the edge is `> n + 1`, we give a trash value -/
      if h₁ : n + 1 < X.dist v₀ (X.target v₀ e) then 0
      else
        /- if the norm of the edge is `≤ n`, we use the induction hypothesis -/
        if h₂ : X.dist v₀ (X.target v₀ e) ≤ n then aux n e
        else
          /- if the norm of the edge is `n + 1`, it is on the current border, so we compute -/
          have he : X.dist v₀ (X.target v₀ e) = n + 1 := by omega
          auxBorder w f v₀ n (aux n) e he
def preimage (e : X.edgeSet) : M :=
  aux w f v₀ (X.dist v₀ (X.target v₀ e)) e
end Construction
end Tree
end Surjectivity
section Hom
variable {X : SimpleGraph V}
variable [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ)
lemma laplace_apply (f : X.edgeSet → M) (v : V) :
    laplace w f v = w v • ∑ e ∈ X.incidenceFinset' v, f e :=
  rfl
@[simp]
lemma laplace_zero : X.laplace w (M := M) 0 = 0 := by
  ext x
  simp [laplace_apply]
@[simp]
lemma laplace_add (f g : X.edgeSet → M) : X.laplace w (f + g) = X.laplace w f + X.laplace w g := by
  ext x
  simp [laplace_apply, Finset.sum_add_distrib, mul_add]
@[simps]
def laplaceHom : (X.edgeSet → M) →+ (V → M) where
  toFun := X.laplace w
  map_zero' := laplace_zero w
  map_add' := laplace_add w
@[simp]
lemma laplace_ASmul (a : A) (f : X.edgeSet → M) : X.laplace w (a • f) = a • X.laplace w f := by
  ext v
  simp [laplace_apply ,smul_comm a (w v), smul_left_cancel_iff, Finset.smul_sum]
lemma isLinearMap_laplace : IsLinearMap A (X.laplace (M := M) w) where
  map_add := laplace_add w
  map_smul := laplace_ASmul w
def laplaceLinearMap : (X.edgeSet → M) →ₗ[A] (V → M) := (isLinearMap_laplace w).mk'
@[simp]
lemma coe_laplaceLinearMap : ⇑(laplaceLinearMap w) = laplace (X := X) (M := M) w :=
  rfl
end Hom
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {V : Type*} [DecidableEq V]
variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]
attribute [instance] arrowAction
section
variable {G A B : Type*} [DivisionMonoid G] [MulAction G A]
@[simp]
lemma arrowAction_apply (g : G) (f : A → B) (a : A) : (g • f) a = f (g⁻¹ • a) :=
  rfl
instance arrowDistribMulAction [AddMonoid B] : DistribMulAction G (A → B) where
  smul_zero g := by ext; simp
  smul_add g x y := by ext; simp
end
instance : SMul G Rˣ where
  smul _ x := x
omit [Group G] in
@[simp]
lemma smul_units (g : G) (x : Rˣ) : g • x = x := rfl
variable {G} {X}
variable [∀ v, Fintype (X.neighborSet v)] (w : V →[G] Rˣ)
@[simp]
lemma laplace_smul (g : G) (f : X.edgeSet → M) :
    laplace w (g • f) = g • laplace w f := by
  ext v
  simp only [laplace_apply, arrowAction_apply, map_smul, smul_units, smul_left_cancel_iff]
  let eq : X.edgeSet ≃ X.edgeSet := {
    toFun := fun e ↦ g⁻¹ • e
    invFun := fun e ↦ g • e
    left_inv := fun e ↦ by simp
    right_inv := fun e ↦ by simp
  }
  refine Finset.sum_equiv eq (fun e ↦ ?_) (fun e _ ↦ ?_)
  · simp [mem_incidenceFinset', eq]
  · simp [eq]
noncomputable
def laplaceSMulHom : (X.edgeSet → M) →+[G] (V → M) where
  toFun := X.laplace w
  map_smul' := laplace_smul w
  map_zero' := laplace_zero w
  map_add' := laplace_add w
end SimpleGraph


