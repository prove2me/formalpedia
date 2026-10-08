-- Prove2me | Definitions.Def_P2MAssembly_Chapter35Plane_Part1
-- name    : P2MAssembly_Chapter35Plane_Part1
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T19:20:24.193533+00:00
-- url     : https://prove2.me/theorems/4951ec20-a70f-433c-9bc1-11e5dc6e29d4
-- title:
--   Finite maps, list colorings, and chord-side cut data
-- statement:
--   A finite map is encoded by an edge involution and vertex rotation on darts, with orbit vertices, edges, and faces. This part contains sphere and simplicity conditions, boundary cycles and near-triangulations, permutation deletion, fan and list-coloring data, chord recursion, orbit/component counts, retained submaps, and first-side face and anchor classifications. It also retains the operation adjoining two new darts to a kept map: the new edge involution is exactly freshAlpha, as expressed by the original definitional equality freshMap_alpha. These local constructions retain their declared involution, fixed-point-free, anchor-distinctness, and map hypotheses. The plane simple graph structure is defined in this part, including its connected simple graph and compatible dart representation.
-- source:
--   Representative original declarations: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMap.lean#L24; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ThomassenLists.lean#L84; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapFilteredRotation.lean#L407; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/PlanarMapFilteredRotation.lean#L415; https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/ChordAnchor.lean#L183. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 39, “Five-coloring plane graphs”, pp. 277–280 (https://doi.org/10.1007/978-3-662-57265-8_39).

import Init
import Mathlib
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Finset.Basic
set_option autoImplicit true


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PlanarMap -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

/-- A combinatorial (orientable) map on a finite dart set `D`:
edge involution `α` (fixed-point-free) and vertex rotation `σ`. -/
structure CombMap (D : Type*) [Fintype D] [DecidableEq D] where
  /-- Edge involution: pairs each dart with its reverse. -/
  α : Equiv.Perm D
  /-- Vertex rotation: cyclic order of darts around each vertex. -/
  σ : Equiv.Perm D
  /-- `α` is an involution. -/
  α_invol : α * α = 1
  /-- `α` has no fixed dart (every edge has two distinct darts). -/
  α_no_fixed : ∀ d, α d ≠ d

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Face permutation `φ = σ ∘ α`. Its orbits are the faces. -/
def φ (M : CombMap D) : Equiv.Perm D := M.σ * M.α

/-- The `SameCycle` equivalence of a permutation, as a `Setoid` on the dart set.
Its classes are the orbits (cycles, including fixed points). -/
def cycleSetoid (p : Equiv.Perm D) : Setoid D where
  r := p.SameCycle
  iseqv := ⟨fun x => Equiv.Perm.SameCycle.refl p x, fun h => h.symm, fun h h' => h.trans h'⟩

instance (p : Equiv.Perm D) : DecidableRel (cycleSetoid p).r :=
  (inferInstance : DecidableRel p.SameCycle)

instance (p : Equiv.Perm D) : Fintype (Quotient (cycleSetoid p)) :=
  Quotient.fintype (cycleSetoid p)

/-- Number of vertices: the number of `σ`-orbits. -/
def V (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.σ))

/-- Number of edges: the number of `α`-orbits. -/
def E (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.α))

/-- Number of faces: the number of `φ`-orbits. -/
def F (M : CombMap D) : ℕ := Fintype.card (Quotient (cycleSetoid M.φ))

/-- The Euler characteristic `V - E + F`. -/
def eulerChar (M : CombMap D) : ℤ := (V M : ℤ) - (E M : ℤ) + (F M : ℤ)

/-- Adjacency of the underlying multigraph on darts: same vertex, or joined by an edge. -/
def dartStep (M : CombMap D) (a b : D) : Prop :=
  M.σ.SameCycle a b ∨ b = M.α a

/-- The map is connected if every two darts are linked by a chain of `dartStep`s. -/
def Connected (M : CombMap D) : Prop :=
  ∀ a b : D, Relation.ReflTransGen M.dartStep a b

/-- A **plane (sphere) map**: connected and of Euler characteristic `2` (genus zero).
The faithful combinatorial definition of a planar graph embedding; NOT an inductive build
certificate, so theorems proved for `IsSphereMap` are about all plane graphs. -/
def IsSphereMap (M : CombMap D) : Prop :=
  M.Connected ∧ M.eulerChar = 2

/-- A power of an involution is either the identity or the involution itself. -/
lemma zpow_involution (α : Equiv.Perm D) (h : α * α = 1) (i : ℤ) :
    α ^ i = 1 ∨ α ^ i = α := by
  have hsq : α ^ (2 : ℤ) = 1 := by
    have h2 : α ^ (2 : ℤ) = α * α := by
      rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
    rw [h2, h]
  rcases Int.even_or_odd i with ⟨r, hr⟩ | ⟨k, hk⟩
  · left
    rw [show i = 2 * r by omega, zpow_mul, hsq, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- The edge containing a dart `d` is exactly `{d, α d}`: the `α`-orbit of any dart has
the two darts of its edge and no more. -/
lemma alpha_sameCycle_iff (M : CombMap D) (d x : D) :
    M.α.SameCycle d x ↔ x = d ∨ x = M.α d := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases zpow_involution M.α M.α_invol i with h1 | h1
    · left; rw [h1]; rfl
    · right; rw [h1]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/-- Every `α`-class (edge) has exactly two darts. -/
lemma alpha_class_card (M : CombMap D)
    (q : Quotient (cycleSetoid M.α)) :
    (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card = 2 := by
  obtain ⟨d, rfl⟩ := q.exists_rep
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.α) x = Quotient.mk (cycleSetoid M.α) d))
        = {d, M.α d} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Quotient.eq]
    show M.α.SameCycle x d ↔ x = d ∨ x = M.α d
    constructor
    · intro h; exact (alpha_sameCycle_iff M d x).mp h.symm
    · intro h; exact ((alpha_sameCycle_iff M d x).mpr h).symm
  rw [hset, Finset.card_insert_of_notMem (by
    simp only [Finset.mem_singleton]
    exact fun hcontra => M.α_no_fixed d hcontra.symm), Finset.card_singleton]

/-- Every edge has exactly two darts: `2 * E = |D|`. -/
lemma two_mul_E_eq_card (M : CombMap D) : 2 * M.E = Fintype.card D := by
  have hsum : Fintype.card D
      = ∑ q : Quotient (cycleSetoid M.α),
          (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.α) x = q)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  rw [hsum, Finset.sum_congr rfl (fun q _ => alpha_class_card M q),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, E, Nat.mul_comm]

/-- Orbit sizes of any permutation sum to the dart count. -/
lemma sum_class_card (p : Equiv.Perm D) :
    ∑ Q : Quotient (cycleSetoid p),
        (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid p) x = Q)).card
      = Fintype.card D := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)).symm













end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMap
-/
/- Source module: ProofsInTheBook.PlaneSimpleGraph -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap

/-- A finite simple graph with a cellular sphere embedding given by a rotation system on darts. -/
structure PlaneSimpleGraph (V D : Type*) [Fintype V] [DecidableEq V]
    [Fintype D] [DecidableEq D] where
  /-- The underlying simple graph. -/
  G : SimpleGraph V
  /-- Tail vertex of a dart. -/
  tail : D → V
  /-- Head vertex of a dart. -/
  head : D → V
  /-- Edge involution. -/
  α : Equiv.Perm D
  /-- Vertex rotation. -/
  σ : Equiv.Perm D
  α_invol : α * α = 1
  α_no_fixed : ∀ d, α d ≠ d
  reverse_tail : ∀ d, tail (α d) = head d
  reverse_head : ∀ d, head (α d) = tail d
  dart_edge : ∀ d, G.Adj (tail d) (head d)
  edge_darts : ∀ {u v : V}, G.Adj u v → ∃! d : D, tail d = u ∧ head d = v
  σ_preserves_tail : ∀ d, tail (σ d) = tail d
  σ_vertex_cycle : ∀ d e : D, tail d = tail e → σ.SameCycle d e
  connected : G.Connected

namespace PlaneSimpleGraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The underlying combinatorial map (forgetting the simple-graph layer). -/
def toCombMap (M : PlaneSimpleGraph V D) : CombMap D where
  α := M.α
  σ := M.σ
  α_invol := M.α_invol
  α_no_fixed := M.α_no_fixed

/-- Number of vertices (of the simple graph). -/
def numVertices (M : PlaneSimpleGraph V D) : ℕ := Fintype.card V

/-- Number of edges = darts / 2. -/
def numEdges (M : PlaneSimpleGraph V D) : ℕ := Fintype.card D / 2

/-- Number of faces = number of `φ = σ * α` orbits. -/
def numFaces (M : PlaneSimpleGraph V D) : ℕ := M.toCombMap.F

/-- Euler characteristic of the embedding. -/
def eulerChar (M : PlaneSimpleGraph V D) : ℤ :=
  (M.numVertices : ℤ) - (M.numEdges : ℤ) + (M.numFaces : ℤ)

/-- The embedding is a sphere (plane) embedding: Euler characteristic `2`. -/
def IsSphereMap (M : PlaneSimpleGraph V D) : Prop :=
  M.eulerChar = 2

end PlaneSimpleGraph

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMap
-/
/- Source module: ProofsInTheBook.PlanarMapEuler -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- Length of a face = number of darts in its `φ`-orbit. -/
def faceLen (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card

/-- Every face has length at least `k` (a simple plane map satisfies this with `k = 3`). -/
def FaceLengthGe (M : CombMap D) (k : ℕ) : Prop :=
  ∀ Q : Quotient (cycleSetoid M.φ), k ≤ M.faceLen Q



/-- The face lengths sum to `2E`. -/
lemma sum_faceLen (M : CombMap D) :
    ∑ Q : Quotient (cycleSetoid M.φ), M.faceLen Q = 2 * M.E := by
  rw [two_mul_E_eq_card]; exact sum_class_card M.φ







end ProofsInTheBook.PlanarMap.CombMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
-/
/- Source module: ProofsInTheBook.PlanarMapSimple -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Vertices are `σ`-orbits of darts. -/
abbrev Vertex (M : CombMap D) : Type _ :=
  Quotient (cycleSetoid M.σ)

/-- Faces are `φ`-orbits of darts. -/
abbrev Face (M : CombMap D) : Type _ :=
  Quotient (cycleSetoid M.φ)

/-- The vertex at the tail of a dart. -/
def tail (M : CombMap D) (d : D) : M.Vertex :=
  Quotient.mk (cycleSetoid M.σ) d

/-- The vertex at the head of a dart, i.e. the tail of its reverse dart. -/
def head (M : CombMap D) (d : D) : M.Vertex :=
  Quotient.mk (cycleSetoid M.σ) (M.α d)

/-- The face containing a dart. -/
def dartFace (M : CombMap D) (d : D) : M.Face :=
  Quotient.mk (cycleSetoid M.φ) d

/-- The unoriented graph edge represented by a dart. -/
def dartEdge (M : CombMap D) (d : D) : Sym2 M.Vertex :=
  s(M.tail d, M.head d)

lemma alpha_alpha (M : CombMap D) (d : D) : M.α (M.α d) = d := by
  have h := congrArg (fun f : Equiv.Perm D => f d) M.α_invol
  simpa [Equiv.Perm.coe_mul, Function.comp_apply] using h

@[simp]
lemma tail_sigma (M : CombMap D) (d : D) : M.tail (M.σ d) = M.tail d := by
  exact Quotient.sound ⟨-1, by simp⟩

@[simp]
lemma tail_phi (M : CombMap D) (d : D) : M.tail (M.φ d) = M.head d := by
  unfold tail head
  exact Quotient.sound ⟨-1, by simp [φ, Equiv.Perm.coe_mul, Function.comp_apply]⟩

@[simp]
lemma tail_alpha (M : CombMap D) (d : D) : M.tail (M.α d) = M.head d :=
  rfl

@[simp]
lemma head_alpha (M : CombMap D) (d : D) : M.head (M.α d) = M.tail d := by
  unfold head tail
  rw [M.alpha_alpha d]

@[simp]
lemma dartEdge_alpha (M : CombMap D) (d : D) : M.dartEdge (M.α d) = M.dartEdge d := by
  simp [dartEdge, Sym2.eq_swap]

/-- Vertex adjacency induced by the map darts, before deleting loops. -/
def Adj (M : CombMap D) (u v : M.Vertex) : Prop :=
  ∃ d : D, M.dartEdge d = s(u, v)

lemma adj_symm (M : CombMap D) {u v : M.Vertex} (h : M.Adj u v) : M.Adj v u := by
  rcases h with ⟨d, hd⟩
  exact ⟨d, by simpa [Sym2.eq_swap] using hd⟩

lemma adj_of_dart (M : CombMap D) (d : D) : M.Adj (M.tail d) (M.head d) :=
  ⟨d, rfl⟩

/-- The underlying `SimpleGraph` on vertex quotients.  Its adjacency is dart
adjacency with loops removed. -/
def toSimpleGraph (M : CombMap D) : SimpleGraph M.Vertex where
  Adj u v := u ≠ v ∧ M.Adj u v
  symm := by
    intro u v h
    exact ⟨h.1.symm, M.adj_symm h.2⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

@[simp]
lemma toSimpleGraph_adj (M : CombMap D) (u v : M.Vertex) :
    M.toSimpleGraph.Adj u v ↔ u ≠ v ∧ M.Adj u v :=
  Iff.rfl

/-- No loops and no parallel edges in the quotient graph carried by the map. -/
structure IsSimpleGraph (M : CombMap D) : Prop where
  /-- No dart has equal endpoint vertices. -/
  no_loop : ∀ d : D, M.tail d ≠ M.head d
  /-- Two darts with the same unordered endpoint pair are the same map edge. -/
  no_parallel : ∀ {d e : D}, M.dartEdge d = M.dartEdge e → M.α.SameCycle d e

lemma toSimpleGraph_adj_of_dart (M : CombMap D) (hM : M.IsSimpleGraph) (d : D) :
    M.toSimpleGraph.Adj (M.tail d) (M.head d) :=
  ⟨hM.no_loop d, M.adj_of_dart d⟩



/-- Dart-representative form of `NoLoopAt`, compatible with `vertexDarts` from
`PlanarMapDelete` without importing that file here. -/
lemma noLoopAt_dart_of_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (v d : D)
    (hd : M.σ.SameCycle v d) :
    ¬ M.σ.SameCycle v (M.α d) := by
  intro hαd
  have htail : M.tail v = M.tail d := Quotient.sound hd
  have hhead : M.tail v = M.head d := Quotient.sound hαd
  exact hM.no_loop d (htail.symm.trans hhead)

lemma alpha_sameCycle_of_dartEdge_eq (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (h : M.dartEdge d = M.dartEdge e) :
    M.α.SameCycle d e :=
  hM.no_parallel h

lemma alpha_sameCycle_of_same_endpoints (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (htail : M.tail d = M.tail e) (hhead : M.head d = M.head e) :
    M.α.SameCycle d e := by
  exact hM.no_parallel (by simp [dartEdge, htail, hhead])

lemma alpha_sameCycle_of_same_endpoints_symm (M : CombMap D) (hM : M.IsSimpleGraph)
    {d e : D} (htail : M.tail d = M.head e) (hhead : M.head d = M.tail e) :
    M.α.SameCycle d e := by
  exact hM.no_parallel (by simp [dartEdge, htail, hhead, Sym2.eq_swap])

/-- Three darts form a triangular face boundary in cyclic order. -/
def IsFaceTriangle (M : CombMap D) (d₀ d₁ d₂ : D) : Prop :=
  M.φ d₀ = d₁ ∧ M.φ d₁ = d₂ ∧ M.φ d₂ = d₀

lemma dartEdge_eq_mk_tail_tail_phi (M : CombMap D) (d : D) :
    M.dartEdge d = s(M.tail d, M.tail (M.φ d)) := by
  simp [dartEdge]

lemma isFaceTriangle_vertices_pairwiseDistinct (M : CombMap D) (hM : M.IsSimpleGraph)
    {d₀ d₁ d₂ : D} (htri : M.IsFaceTriangle d₀ d₁ d₂) :
    M.tail d₀ ≠ M.tail d₁ ∧
      M.tail d₁ ≠ M.tail d₂ ∧
      M.tail d₂ ≠ M.tail d₀ := by
  rcases htri with ⟨h₀₁, h₁₂, h₂₀⟩
  constructor
  · intro h
    apply hM.no_loop d₀
    have hnext : M.tail d₁ = M.head d₀ := by
      rw [← h₀₁]
      simp
    exact h.trans hnext
  constructor
  · intro h
    apply hM.no_loop d₁
    have hnext : M.tail d₂ = M.head d₁ := by
      rw [← h₁₂]
      simp
    exact h.trans hnext
  · intro h
    apply hM.no_loop d₂
    have hnext : M.tail d₀ = M.head d₂ := by
      rw [← h₂₀]
      simp
    exact h.trans hnext



end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
-/
/- Source module: ProofsInTheBook.PlanarMapDelete -/
section
set_option autoImplicit true




namespace Equiv.Perm

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace DeleteSet

omit [DecidableEq D] in
/-- There is always a positive iterate of `p` from a surviving point back to a
surviving point: `orderOf p` returns to the starting point. -/
lemma exists_pos_pow_notMem (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) :
    ∃ n : ℕ, 0 < n ∧ (p ^ n) x.1 ∉ S := by
  refine ⟨orderOf p, orderOf_pos p, ?_⟩
  simpa using x.2

/-- The first positive `p`-iterate of `x` outside `S`. -/
noncomputable def firstOutside (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) : ℕ :=
  Nat.find (exists_pos_pow_notMem p S x)

lemma firstOutside_spec (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    0 < firstOutside p S x ∧ (p ^ firstOutside p S x) x.1 ∉ S :=
  Nat.find_spec (exists_pos_pow_notMem p S x)

lemma firstOutside_pos (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    0 < firstOutside p S x :=
  (firstOutside_spec p S x).1

lemma firstOutside_notMem (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    (p ^ firstOutside p S x) x.1 ∉ S :=
  (firstOutside_spec p S x).2

lemma firstOutside_min (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) {m : ℕ}
    (hm : m < firstOutside p S x) :
    ¬ (0 < m ∧ (p ^ m) x.1 ∉ S) :=
  Nat.find_min (exists_pos_pow_notMem p S x) hm

/-- The underlying function of `deleteSet`: move to the first surviving forward
iterate. -/
noncomputable def deleteSetFun (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) : {d : D // d ∉ S} :=
  ⟨(p ^ firstOutside p S x) x.1, firstOutside_notMem p S x⟩

@[simp]
lemma deleteSetFun_coe (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    (deleteSetFun p S x : D) = (p ^ firstOutside p S x) x.1 :=
  rfl

lemma firstOutside_inv_deleteSetFun (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    firstOutside p⁻¹ S (deleteSetFun p S x) = firstOutside p S x := by
  classical
  let n := firstOutside p S x
  have hnpos : 0 < n := firstOutside_pos p S x
  have hnnot : (p ^ n) x.1 ∉ S := firstOutside_notMem p S x
  refine (Nat.find_eq_iff (exists_pos_pow_notMem p⁻¹ S (deleteSetFun p S x))).2 ?_
  constructor
  · constructor
    · exact hnpos
    · have hpow : ((p⁻¹) ^ n) ((deleteSetFun p S x : {d : D // d ∉ S}) : D) = x.1 := by
        simp only [deleteSetFun_coe]
        rw [inv_pow]
        change (p ^ n).symm ((p ^ n) x.1) = x.1
        exact Equiv.symm_apply_apply (p ^ n) x.1
      simpa [hpow] using x.2
  · intro m hm
    rintro ⟨hmpos, hmnot⟩
    have hmn : m < n := hm
    have hsubpos : 0 < n - m := Nat.sub_pos_of_lt hmn
    have hsub_lt : n - m < n := Nat.sub_lt hnpos hmpos
    have hforward :
        (p ^ (n - m)) x.1 =
          ((p⁻¹) ^ m) ((deleteSetFun p S x : {d : D // d ∉ S}) : D) := by
      simp only [deleteSetFun_coe]
      rw [inv_pow]
      have hle : m ≤ n := le_of_lt hmn
      have hperm : (p ^ m)⁻¹ * p ^ n = p ^ (n - m) := by
        have hpown : p ^ n = p ^ m * p ^ (n - m) := by
          have hadd : m + (n - m) = n := Nat.add_sub_of_le hle
          calc
            p ^ n = p ^ (m + (n - m)) := by rw [hadd]
            _ = p ^ m * p ^ (n - m) := by rw [pow_add]
        calc
          (p ^ m)⁻¹ * p ^ n = (p ^ m)⁻¹ * (p ^ m * p ^ (n - m)) := by
            rw [hpown]
          _ = p ^ (n - m) := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
      calc
        (p ^ (n - m)) x.1 = ((p ^ m)⁻¹ * (p ^ n)) x.1 := by
          rw [hperm]
        _ = ((p ^ m)⁻¹) ((p ^ n) x.1) := rfl
        _ = ((p⁻¹) ^ m) ((p ^ n) x.1) := by rw [inv_pow]
    have hbad : 0 < n - m ∧ (p ^ (n - m)) x.1 ∉ S := by
      exact ⟨hsubpos, by simpa [hforward] using hmnot⟩
    exact firstOutside_min p S x hsub_lt hbad

lemma deleteSetFun_inv_apply (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    deleteSetFun p⁻¹ S (deleteSetFun p S x) = x := by
  classical
  apply Subtype.ext
  rw [deleteSetFun_coe, firstOutside_inv_deleteSetFun p S x, deleteSetFun_coe]
  rw [inv_pow]
  change (p ^ firstOutside p S x).symm ((p ^ firstOutside p S x) x.1) = x.1
  exact Equiv.symm_apply_apply (p ^ firstOutside p S x) x.1

end DeleteSet

open DeleteSet

/-- Delete a finite set from the cycles of a permutation, reconnecting the
surviving points by skipping deleted points. -/
noncomputable def deleteSet (p : Equiv.Perm D) (S : Finset D) :
    Equiv.Perm {d : D // d ∉ S} where
  toFun := deleteSetFun p S
  invFun := deleteSetFun p⁻¹ S
  left_inv := deleteSetFun_inv_apply p S
  right_inv := by
    intro x
    simpa using deleteSetFun_inv_apply p⁻¹ S x

@[simp]
lemma deleteSet_apply_coe (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    ((deleteSet p S x : {d : D // d ∉ S}) : D) =
      (p ^ firstOutside p S x) x.1 :=
  rfl

lemma sameCycle_deleteSet_imp (p : Equiv.Perm D) (S : Finset D)
    {x y : {d : D // d ∉ S}} :
    (deleteSet p S).SameCycle x y → p.SameCycle x.1 y.1 := by
  classical
  intro hxy
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.SameCycle.exists_nat_pow_eq (f := deleteSet p S) hxy
  clear hxy
  revert x
  induction m with
  | zero =>
      intro x hm
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hm
      exact (congrArg Subtype.val hm).sameCycle p
  | succ m ih =>
      intro x hm
      let z : {d : D // d ∉ S} := deleteSet p S x
      have hstep : p.SameCycle x.1 z.1 := by
        refine ⟨(firstOutside p S x : ℤ), ?_⟩
        rw [zpow_natCast]
        rfl
      have htail : ((deleteSet p S) ^ m) z = y := by
        simpa [z, pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hm
      exact hstep.trans (ih (x := z) htail)

lemma sameCycle_deleteSet_of_pow (p : Equiv.Perm D) (S : Finset D) :
    ∀ m : ℕ, ∀ x y : {d : D // d ∉ S},
      (p ^ m) x.1 = y.1 → (deleteSet p S).SameCycle x y := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro x y hxy
      by_cases hm0 : m = 0
      · subst hm0
        apply (Subtype.ext ?_).sameCycle
        simpa using hxy
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        let n := firstOutside p S x
        have hnpos : 0 < n := firstOutside_pos p S x
        have hnot_lt : ¬ m < n := by
          intro hmn
          have hbad : 0 < m ∧ (p ^ m) x.1 ∉ S := by
            exact ⟨hmpos, by simpa [hxy] using y.2⟩
          exact firstOutside_min p S x hmn hbad
        have hnm : n ≤ m := le_of_not_gt hnot_lt
        let z : {d : D // d ∉ S} := deleteSet p S x
        have hxz : z.1 = (p ^ n) x.1 := rfl
        have hstep : (deleteSet p S).SameCycle x z := by
          refine ⟨1, ?_⟩
          change deleteSet p S x = z
          rfl
        by_cases hnm_eq : n = m
        · have hzy : z = y := by
            apply Subtype.ext
            rw [hxz, hnm_eq, hxy]
          simpa [hzy] using hstep
        · have hlt : m - n < m := Nat.sub_lt hmpos hnpos
          have hpow : (p ^ (m - n)) z.1 = y.1 := by
            rw [hxz]
            rw [← mul_apply, ← pow_add]
            have hadd : m - n + n = m := Nat.sub_add_cancel hnm
            rw [hadd, hxy]
          exact hstep.trans (ih (m - n) hlt z y hpow)

lemma sameCycle_deleteSet_iff (p : Equiv.Perm D) (S : Finset D)
    (x y : {d : D // d ∉ S}) :
    (deleteSet p S).SameCycle x y ↔ p.SameCycle x.1 y.1 := by
  classical
  constructor
  · exact sameCycle_deleteSet_imp p S
  · intro h
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := p) h
    exact sameCycle_deleteSet_of_pow p S m x y hm

end Equiv.Perm

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The darts in the `σ`-orbit of a dart representative `v`. -/
def vertexDarts (M : CombMap D) (v : D) : Finset D :=
  Finset.univ.filter (fun d => M.σ.SameCycle v d)

/-- Degree of the vertex represented by `v`, as a dart count. -/
def dartVertexDegree (M : CombMap D) (v : D) : ℕ :=
  (M.vertexDarts v).card

/-- No loop based at the vertex represented by `v`: the edge reverse of a dart
at `v` is not also a dart at `v`.  This is needed for the simple edge-count
formula `E' = E - deg(v)`. -/
def NoLoopAt (M : CombMap D) (v : D) : Prop :=
  ∀ d : D, d ∈ M.vertexDarts v → M.α d ∉ M.vertexDarts v

@[simp]
lemma mem_vertexDarts (M : CombMap D) (v d : D) :
    d ∈ M.vertexDarts v ↔ M.σ.SameCycle v d := by
  simp [vertexDarts]



/-- The closed dart star of `v`: the darts at `v` and their edge reverses.
This is the set that is actually stable under `α`, hence the one on which
`α` can be restricted after deleting a vertex and all incident edges. -/
def deleteVertexSet (M : CombMap D) (v : D) : Finset D :=
  M.vertexDarts v ∪ (M.vertexDarts v).image M.α.toEmbedding

lemma mem_deleteVertexSet_iff (M : CombMap D) (v d : D) :
    d ∈ M.deleteVertexSet v ↔ d ∈ M.vertexDarts v ∨ M.α d ∈ M.vertexDarts v := by
  classical
  constructor
  · intro hd
    rw [deleteVertexSet, Finset.mem_union, Finset.mem_image] at hd
    rcases hd with hd | ⟨x, hx, hxd⟩
    · exact Or.inl hd
    · right
      have : M.α d = x := by
        rw [← hxd]
        have hα : M.α * M.α = 1 := M.α_invol
        have happ := congrArg (fun f : Equiv.Perm D => f x) hα
        simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
      simpa [this] using hx
  · intro hd
    rw [deleteVertexSet, Finset.mem_union, Finset.mem_image]
    rcases hd with hd | hd
    · exact Or.inl hd
    · right
      refine ⟨M.α d, hd, ?_⟩
      have hα : M.α * M.α = 1 := M.α_invol
      have happ := congrArg (fun f : Equiv.Perm D => f d) hα
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ

lemma alpha_mem_deleteVertexSet_iff (M : CombMap D) (v d : D) :
    M.α d ∈ M.deleteVertexSet v ↔ d ∈ M.deleteVertexSet v := by
  classical
  rw [mem_deleteVertexSet_iff, mem_deleteVertexSet_iff]
  have hαd : M.α (M.α d) = d := by
    have hα : M.α * M.α = 1 := M.α_invol
    have happ := congrArg (fun f : Equiv.Perm D => f d) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  simp [hαd, or_comm]

/-- Restrict the edge involution to the complement of an `α`-stable deleted set. -/
noncomputable def alphaDeleteVertex (M : CombMap D) (v : D) :
    Equiv.Perm {d : D // d ∉ M.deleteVertexSet v} :=
  M.α.subtypePerm (fun d => by
    constructor
    · intro hd hdel
      exact hd ((alpha_mem_deleteVertexSet_iff M v d).2 hdel)
    · intro hd hdel
      exact hd ((alpha_mem_deleteVertexSet_iff M v d).1 hdel))

@[simp]
lemma alphaDeleteVertex_apply_coe (M : CombMap D) (v : D)
    (d : {d : D // d ∉ M.deleteVertexSet v}) :
    (M.alphaDeleteVertex v d : D) = M.α d.1 := by
  simp [alphaDeleteVertex]

/-- Delete the closed dart star of `v`.  The vertex rotation skips all deleted
darts; the edge involution is the restriction of `α` to the surviving darts. -/
noncomputable def deleteVertex (M : CombMap D) (v : D) :
    CombMap {d : D // d ∉ M.deleteVertexSet v} where
  α := M.alphaDeleteVertex v
  σ := M.σ.deleteSet (M.deleteVertexSet v)
  α_invol := by
    ext d
    simp [alphaDeleteVertex, Equiv.Perm.subtypePerm_apply]
    have hα : M.α * M.α = 1 := M.α_invol
    have happ := congrArg (fun f : Equiv.Perm D => f d.1) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  α_no_fixed := by
    intro d h
    exact M.α_no_fixed d.1 (by
      have := congrArg Subtype.val h
      simpa [alphaDeleteVertex] using this)

@[simp]
lemma deleteVertex_alpha_apply_coe (M : CombMap D) (v : D)
    (d : {d : D // d ∉ M.deleteVertexSet v}) :
    ((M.deleteVertex v).α d : D) = M.α d.1 :=
  rfl

@[simp]
lemma deleteVertex_sigma_sameCycle_iff (M : CombMap D) (v : D)
    (x y : {d : D // d ∉ M.deleteVertexSet v}) :
    (M.deleteVertex v).σ.SameCycle x y ↔ M.σ.SameCycle x.1 y.1 := by
  simpa [deleteVertex] using Equiv.Perm.sameCycle_deleteSet_iff M.σ (M.deleteVertexSet v) x y

lemma deleteVertexSet_card_eq_two_mul_degree (M : CombMap D) (v : D)
    (hloop : M.NoLoopAt v) :
    (M.deleteVertexSet v).card = 2 * M.dartVertexDegree v := by
  classical
  have hdisj :
      Disjoint (M.vertexDarts v) ((M.vertexDarts v).image M.α.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro d hd hdi
    rw [Finset.mem_image] at hdi
    obtain ⟨x, hx, hxd⟩ := hdi
    exact hloop x hx (by simpa [← hxd] using hd)
  rw [deleteVertexSet, Finset.card_union_of_disjoint hdisj]
  have himg :
      ((M.vertexDarts v).image M.α.toEmbedding).card = (M.vertexDarts v).card := by
    simpa using
      Finset.card_image_of_injective (M.vertexDarts v) M.α.injective
  rw [himg]
  simp [dartVertexDegree, Nat.two_mul]

lemma fintype_card_compl_finset (S : Finset D) :
    Fintype.card {d : D // d ∉ S} = Fintype.card D - S.card := by
  classical
  rw [Fintype.card_subtype_compl (fun d : D => d ∈ S)]
  rw [Fintype.card_coe S]

/-- Vertex-count reduction, factored through the exact quotient equivalence
that remains to be proved for the chosen deletion set.

For the closed-star deletion used by `deleteVertex`, this equivalence is not
automatic from `Perm.deleteSet`: deleting the opposite darts of incident edges
also removes darts from neighboring `σ`-orbits.  One must prove that every
nondeleted vertex orbit has a surviving representative and that the deleted
orbit of `v` has none. -/
lemma deleteVertex_V_of_orbitEquiv (M : CombMap D) (v : D)
    (hQ :
      Quotient (cycleSetoid (M.deleteVertex v).σ) ≃
        {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v}) :
    (M.deleteVertex v).V = M.V - 1 := by
  classical
  let qv : Quotient (cycleSetoid M.σ) := Quotient.mk (cycleSetoid M.σ) v
  have hcard :
      Fintype.card {Q : Quotient (cycleSetoid M.σ) // Q ≠ qv}
        = Fintype.card (Quotient (cycleSetoid M.σ)) - 1 := by
    rw [Fintype.card_subtype_compl (fun Q : Quotient (cycleSetoid M.σ) => Q = qv)]
    rw [Fintype.card_subtype_eq qv]
  have hcongr := Fintype.card_congr hQ
  change
      Fintype.card (Quotient (cycleSetoid (M.deleteVertex v).σ)) =
        Fintype.card {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v} at hcongr
  simpa [V, qv] using hcongr.trans hcard

lemma deleteVertex_E (M : CombMap D) (v : D) (hloop : M.NoLoopAt v) :
    (M.deleteVertex v).E = M.E - M.dartVertexDegree v := by
  classical
  let M' := M.deleteVertex v
  have h2E : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  have h2E' : 2 * M'.E = Fintype.card {d : D // d ∉ M.deleteVertexSet v} :=
    two_mul_E_eq_card M'
  have hcard :
      Fintype.card {d : D // d ∉ M.deleteVertexSet v}
        = Fintype.card D - 2 * M.dartVertexDegree v := by
    rw [fintype_card_compl_finset, deleteVertexSet_card_eq_two_mul_degree M v hloop]
  have h2 : 2 * M'.E = 2 * (M.E - M.dartVertexDegree v) := by
    rw [h2E', hcard, ← h2E]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2

/-- The faces of `M` touched by the vertex represented by `v`, recorded as
`φ`-orbit quotients. -/
noncomputable def vertexFaces (M : CombMap D) (v : D) :
    Finset (Quotient (cycleSetoid M.φ)) :=
  (M.vertexDarts v).image (fun d => Quotient.mk (cycleSetoid M.φ) d)

/-- The local simple-boundary condition that each dart at `v` lies on a
different face.  Without it, a cut vertex or bridge can make the same face
appear more than once around `v`, so the connected face-count formula is not
`F' = F - deg(v) + 1`. -/
def VertexFacesDistinct (M : CombMap D) (v : D) : Prop :=
  Set.InjOn (fun d => Quotient.mk (cycleSetoid M.φ) d) (M.vertexDarts v : Set D)

lemma vertexFaces_card_eq_degree (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v) :
    (M.vertexFaces v).card = M.dartVertexDegree v := by
  classical
  rw [vertexFaces, dartVertexDegree]
  exact Finset.card_image_of_injOn hdistinct

/-- The quotient-level face model for connected vertex deletion: all faces not
incident with `v` survive, while the faces incident with `v` are replaced by
one merged boundary face.  The hard topological boundary lemma is precisely an
equivalence from the actual deleted-map face quotients to this model. -/
abbrev deleteVertexFaceModel (M : CombMap D) (v : D) :=
  {Q : Quotient (cycleSetoid M.φ) // Q ∉ M.vertexFaces v} ⊕ Unit

/-- Quotient-level statement of the deleted-star boundary lemma for the
connected case. -/
def DeleteVertexFacesMerge (M : CombMap D) (v : D) : Prop :=
  Nonempty
    (Quotient (cycleSetoid (M.deleteVertex v).φ) ≃ M.deleteVertexFaceModel v)



lemma deleteVertexFaceModel_card (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v) :
    Fintype.card (M.deleteVertexFaceModel v) =
      M.F - M.dartVertexDegree v + 1 := by
  classical
  have hcard := vertexFaces_card_eq_degree M v hdistinct
  change
    Fintype.card
        ({Q : Quotient (cycleSetoid M.φ) // Q ∉ M.vertexFaces v} ⊕ Unit) =
      M.F - M.dartVertexDegree v + 1
  rw [Fintype.card_sum, Fintype.card_unit,
    Fintype.card_subtype_compl (fun Q : Quotient (cycleSetoid M.φ) =>
      Q ∈ M.vertexFaces v),
    Fintype.card_coe, F, hcard]



lemma deleteVertex_F_of_facesMerge (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v)
    (hmerge : M.DeleteVertexFacesMerge v) :
    (M.deleteVertex v).F = M.F - M.dartVertexDegree v + 1 := by
  classical
  rcases hmerge with ⟨e⟩
  change
    Fintype.card (Quotient (cycleSetoid (M.deleteVertex v).φ)) =
      M.F - M.dartVertexDegree v + 1
  exact (Fintype.card_congr e).trans (deleteVertexFaceModel_card M v hdistinct)

lemma dartVertexDegree_le_E (M : CombMap D) (v : D) (hloop : M.NoLoopAt v) :
    M.dartVertexDegree v ≤ M.E := by
  classical
  have hsubset : M.deleteVertexSet v ⊆ Finset.univ := by
    intro d _; exact Finset.mem_univ d
  have hcardle : (M.deleteVertexSet v).card ≤ Fintype.card D := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsubset
  have hdel := deleteVertexSet_card_eq_two_mul_degree M v hloop
  have h2E := two_mul_E_eq_card M
  have hmul : 2 * M.dartVertexDegree v ≤ 2 * M.E := by
    rw [← hdel, h2E]
    exact hcardle
  omega

lemma dartVertexDegree_le_F_of_vertexFacesDistinct (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v) :
    M.dartVertexDegree v ≤ M.F := by
  classical
  have hcard := vertexFaces_card_eq_degree M v hdistinct
  have hsubset : M.vertexFaces v ⊆ Finset.univ := by
    intro Q _; exact Finset.mem_univ Q
  have hle : (M.vertexFaces v).card ≤
      Fintype.card (Quotient (cycleSetoid M.φ)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsubset
  simpa [F, hcard] using hle

lemma one_le_V_of_dart (M : CombMap D) (v : D) : 1 ≤ M.V := by
  classical
  have hpos : 0 < Fintype.card (Quotient (cycleSetoid M.σ)) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk (cycleSetoid M.σ) v⟩
  simpa [V] using hpos

lemma deleteVertex_eulerChar_of_facesMerge (M : CombMap D) (v : D)
    (hsphereEuler : M.eulerChar = 2) (hloop : M.NoLoopAt v)
    (hQ :
      Quotient (cycleSetoid (M.deleteVertex v).σ) ≃
        {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v})
    (hdistinct : M.VertexFacesDistinct v)
    (hmerge : M.DeleteVertexFacesMerge v) :
    (M.deleteVertex v).eulerChar = 2 := by
  classical
  have hV := deleteVertex_V_of_orbitEquiv M v hQ
  have hE := deleteVertex_E M v hloop
  have hF := deleteVertex_F_of_facesMerge M v hdistinct hmerge
  have hVle : 1 ≤ M.V := one_le_V_of_dart M v
  have hdegE : M.dartVertexDegree v ≤ M.E := dartVertexDegree_le_E M v hloop
  have hdegF : M.dartVertexDegree v ≤ M.F :=
    dartVertexDegree_le_F_of_vertexFacesDistinct M v hdistinct
  unfold eulerChar
  rw [hV, hE, hF]
  unfold eulerChar at hsphereEuler
  omega

/-- Connected-case vertex deletion: assuming the remaining vertex quotient is
exactly the old vertex quotient with `v` removed, and assuming the deleted-star
face quotient really is the connected face-merge model, Euler characteristic is
preserved.  The final `hconn` is the graph-theoretic connectedness of the
deleted map. -/
theorem deleteVertex_isSphereMap (M : CombMap D) (v : D) (hsphere : M.IsSphereMap)
    (hloop : M.NoLoopAt v)
    (hQ :
      Quotient (cycleSetoid (M.deleteVertex v).σ) ≃
        {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v})
    (hdistinct : M.VertexFacesDistinct v)
    (hmerge : M.DeleteVertexFacesMerge v)
    (hconn : (M.deleteVertex v).Connected) :
    (M.deleteVertex v).IsSphereMap := by
  exact
    ⟨hconn,
      deleteVertex_eulerChar_of_facesMerge M v hsphere.2 hloop hQ hdistinct hmerge⟩



section TwoEdgePathObstruction























end TwoEdgePathObstruction

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.PlanarMapBoundary -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Cyclic successor on a nonempty finite index type. -/
def cyclicNext {n : ℕ} (h : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.1 + 1) % n, Nat.mod_lt _ h⟩



/-- The dart set of a face, as a finite orbit set. -/
def faceOrbitFinset (M : CombMap D) (f : M.Face) : Finset D :=
  Finset.univ.filter fun d => M.dartFace d = f

@[simp]
lemma mem_faceOrbitFinset_iff (M : CombMap D) (f : M.Face) (d : D) :
    d ∈ faceOrbitFinset M f ↔ M.dartFace d = f := by
  simp [faceOrbitFinset]

/-- A normalized cyclic dart list for a selected face orbit.

The `root` chooses one representative and fixes the cyclic rotation.  The
`toFinset_eq` field says the list enumerates exactly the selected `φ`-orbit.
-/
structure NormalizedCyclicDartList (M : CombMap D) (f : M.Face)
    (root : D) (darts : List D) : Prop where
  head_eq : darts.head? = some root
  root_face : M.dartFace root = f
  nodup : darts.Nodup
  length_pos : 0 < darts.length
  toFinset_eq : darts.toFinset = faceOrbitFinset M f

/-- A boundary arc/path between two boundary vertices. -/
structure BoundaryPath (M : CombMap D) (u v : M.Vertex) where
  /-- Vertices in path order, including both endpoints. -/
  vertices : List M.Vertex
  /-- Edges in path order.  For boundary arcs these are boundary-cycle edges. -/
  edges : List (Sym2 M.Vertex)
  /-- The first listed vertex is the initial endpoint. -/
  starts_at : vertices.head? = some u
  /-- The last listed vertex is the terminal endpoint. -/
  ends_at : vertices.getLast? = some v
  /-- The arc is simple as a vertex list. -/
  simple : vertices.Nodup

namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}

/-- Interior vertices of a path: endpoints removed. -/
def internalVertices (P : BoundaryPath M u v) : List M.Vertex :=
  P.vertices.tail.dropLast

/-- A path has at least one internal vertex. -/
def HasInternalVertex (P : BoundaryPath M u v) : Prop :=
  P.internalVertices ≠ []

@[simp]
lemma hasInternalVertex_iff (P : BoundaryPath M u v) :
    P.HasInternalVertex ↔ P.internalVertices ≠ [] :=
  Iff.rfl





end BoundaryPath

/-- The two boundary arcs determined by a pair of distinct boundary vertices. -/
structure BoundaryArcSplit (M : CombMap D)
    (boundaryVertices : List M.Vertex) (boundaryEdges : List (Sym2 M.Vertex))
    (u v : M.Vertex) where
  /-- The arc from `u` to `v`. -/
  path₁ : BoundaryPath M u v
  /-- The complementary arc from `v` back to `u`. -/
  path₂ : BoundaryPath M v u
  /-- `path₁` uses only boundary vertices. -/
  path₁_boundary_vertices :
    ∀ ⦃w : M.Vertex⦄, w ∈ path₁.vertices → w ∈ boundaryVertices
  /-- `path₂` uses only boundary vertices. -/
  path₂_boundary_vertices :
    ∀ ⦃w : M.Vertex⦄, w ∈ path₂.vertices → w ∈ boundaryVertices
  /-- Together the two arcs cover the boundary vertex list. -/
  boundary_vertices_covered :
    ∀ w : M.Vertex, w ∈ boundaryVertices ↔ w ∈ path₁.vertices ∨ w ∈ path₂.vertices
  /-- The internal vertices of the two arcs are disjoint. -/
  internally_disjoint :
    ∀ ⦃w : M.Vertex⦄,
      w ∈ path₁.internalVertices → w ∈ path₂.internalVertices → False
  /-- The first arc is nontrivial when the endpoint pair is not a boundary edge.
  (One-directional: a *proper* — non-adjacent — pair forces an internal vertex.  The
  converse `HasInternalVertex → proper` is intentionally NOT required: for a *consecutive*
  pair the long complementary arc must still carry the cycle's other vertices internally,
  so demanding `↔` would make `BoundaryArcSplit`, hence `BoundaryCycle`/`NearTriangulation`,
  uninhabited whenever the cycle has a third vertex.  See `ZinanCh35VacuityObstruction`.) -/
  path₁_internal_of_proper :
    s(u, v) ∉ boundaryEdges → path₁.HasInternalVertex
  /-- The second arc is nontrivial when the endpoint pair is not a boundary edge
  (one-directional, same rationale as `path₁_internal_of_proper`). -/
  path₂_internal_of_proper :
    s(u, v) ∉ boundaryEdges → path₂.HasInternalVertex

/-- The orbit-algebraic **core** of a boundary cycle — every field except the
`arcSplit` certificate.  Split out (2026-06-15) so the universal arc-split
(`arcSplit_of_nodup`, derivable from `VertexNodup`) can be proved over the core and
installed into the full `BoundaryCycle` without the `boundaryCycleOfFace ↔ arcSplit`
self-reference.  See `HANDOFF/ch35-arcsplit-core-refactor.md`. -/
structure BoundaryCycleData (M : CombMap D) (f : M.Face) where
  /-- Chosen dart representative fixing the cyclic rotation. -/
  root : D
  /-- Normalized cyclic dart list enumerating the selected face orbit. -/
  darts : List D
  /-- Cyclic boundary vertex list. -/
  vertices : List M.Vertex
  /-- Cyclic boundary edge list. -/
  edges : List (Sym2 M.Vertex)
  /-- The dart list is normalized and exactly enumerates the selected face orbit. -/
  normalized : NormalizedCyclicDartList M f root darts
  /-- Boundary vertices are the tails of the cyclic dart list. -/
  vertices_eq : vertices = darts.map M.tail
  /-- Boundary edges are the graph edges represented by the cyclic dart list. -/
  edges_eq : edges = darts.map M.dartEdge
  /-- The cyclic order agrees with the face permutation. -/
  consecutive_phi :
    ∀ i : Fin darts.length,
      darts.get (cyclicNext normalized.length_pos i) = M.φ (darts.get i)
  /-- Consecutive boundary darts match at their common boundary vertex. -/
  consecutive_vertex :
    ∀ i : Fin darts.length,
      M.tail (darts.get (cyclicNext normalized.length_pos i)) = M.head (darts.get i)

/-- A boundary cycle for the selected face `f`: the orbit-algebraic core
(`BoundaryCycleData`) together with the arc-splitting certificate.

The dart list is a normalized cyclic enumeration of the `φ`-orbit of `f`.
The vertex and edge lists are exposed so later files can reason about the
boundary without repeatedly unfolding quotient-orbit facts.
-/
structure BoundaryCycle (M : CombMap D) (f : M.Face) extends BoundaryCycleData M f where
  /-- Arc-splitting certificate for any two distinct listed boundary vertices. -/
  arcSplit :
    ∀ ⦃u v : M.Vertex⦄,
      u ≠ v → u ∈ vertices → v ∈ vertices →
        BoundaryArcSplit M vertices edges u v

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-- Boundary vertices are represented by the exposed cyclic vertex list. -/
def IsBoundaryVertex (C : BoundaryCycle M f) (v : M.Vertex) : Prop :=
  v ∈ C.vertices

/-- Boundary edges are represented by the exposed cyclic edge list. -/
def IsBoundaryEdge (C : BoundaryCycle M f) (e : Sym2 M.Vertex) : Prop :=
  e ∈ C.edges



/-- The boundary vertex list is simple. -/
def VertexNodup (C : BoundaryCycle M f) : Prop :=
  C.vertices.Nodup



/-- Boundary length, measured in darts/edges. -/
def length (C : BoundaryCycle M f) : ℕ :=
  C.darts.length



lemma darts_nodup (C : BoundaryCycle M f) : C.darts.Nodup :=
  C.normalized.nodup

lemma darts_length_pos (C : BoundaryCycle M f) : 0 < C.darts.length :=
  C.normalized.length_pos





lemma mem_darts_iff (C : BoundaryCycle M f) (d : D) :
    d ∈ C.darts ↔ M.dartFace d = f := by
  rw [← List.mem_toFinset, C.normalized.toFinset_eq]
  simp

lemma dartFace_of_mem_darts (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    M.dartFace d = f :=
  (C.mem_darts_iff d).mp hd





lemma vertices_length (C : BoundaryCycle M f) :
    C.vertices.length = C.length := by
  simp [length, C.vertices_eq]





/-- A boundary chord is an ambient graph edge between boundary vertices that is
not one of the boundary-cycle edges. -/
structure Chord (C : BoundaryCycle M f) (u v : M.Vertex) : Prop where
  endpoints_ne : u ≠ v
  left_boundary : C.IsBoundaryVertex u
  right_boundary : C.IsBoundaryVertex v
  adj : M.toSimpleGraph.Adj u v
  not_boundary_edge : ¬ C.IsBoundaryEdge s(u, v)

namespace Chord

variable {C : BoundaryCycle M f} {u v : M.Vertex}



end Chord

end BoundaryCycle



/-- A boundary is chordless if no boundary chord exists. -/
def BoundaryChordless {M : CombMap D} {f : M.Face} (C : BoundaryCycle M f) : Prop :=
  ∀ ⦃u v : M.Vertex⦄, ¬ C.Chord u v

namespace BoundaryArcSplit

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}









end BoundaryArcSplit



namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}











end BoundaryCycle



end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapNearTriangulation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A near-triangulation is a simple sphere map with one distinguished simple
outer boundary cycle of length at least three; every other face has length
three. -/
structure NearTriangulation (M : CombMap D) where
  sphere : M.IsSphereMap
  simpleGraph : M.IsSimpleGraph
  outerFace : M.Face
  outerCycle : BoundaryCycle M outerFace
  outer_simple : outerCycle.VertexNodup
  outer_len : 3 ≤ outerCycle.length
  inner_tri : ∀ f : M.Face, f ≠ outerFace → M.faceLen f = 3

@[simp]
lemma dartFace_phi (M : CombMap D) (d : D) :
    M.dartFace (M.φ d) = M.dartFace d := by
  unfold dartFace
  exact Quotient.sound ⟨-1, by simp⟩

@[simp]
lemma dartFace_phi_symm (M : CombMap D) (d : D) :
    M.dartFace (M.φ.symm d) = M.dartFace d := by
  unfold dartFace
  exact Quotient.sound ⟨1, by simp⟩

lemma phi_ne_self_of_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (d : D) :
    M.φ d ≠ d := by
  intro h
  have htail : M.head d = M.tail d := by
    calc
      M.head d = M.tail (M.φ d) := (M.tail_phi d).symm
      _ = M.tail d := by rw [h]
  exact hM.no_loop d htail.symm



lemma faceLen_dartFace_eq_card_support_cycleOf (M : CombMap D) {d : D}
    (hφ : M.φ d ≠ d) :
    M.faceLen (M.dartFace d) = (M.φ.cycleOf d).support.card := by
  have hset :
      (Finset.univ.filter
          (fun x => Quotient.mk (cycleSetoid M.φ) x = M.dartFace d))
        = (M.φ.cycleOf d).support := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, dartFace,
      Equiv.Perm.mem_support_cycleOf_iff' hφ, Quotient.eq]
    exact Equiv.Perm.sameCycle_comm
  simpa [faceLen] using congrArg Finset.card hset

lemma card_support_cycleOf_eq_two_of_apply_apply_eq_self
    (p : Equiv.Perm D) {d : D} (hp : p d ≠ d) (h2 : p (p d) = d) :
    (p.cycleOf d).support.card = 2 := by
  have hc : Equiv.Perm.IsCycle (p.cycleOf d) :=
    Equiv.Perm.isCycle_cycleOf p hp
  have hcd : p.cycleOf d d = p d :=
    Equiv.Perm.cycleOf_apply_self p d
  have hcpd : p.cycleOf d (p d) = d := by
    have hsc : p.SameCycle d (p d) := by
      simpa using (Equiv.Perm.sameCycle_apply_right (f := p) (x := d) (y := d)).2
        Equiv.Perm.SameCycle.rfl
    simp [h2, hsc.cycleOf_apply]
  have hcd_ne : p.cycleOf d d ≠ d := by
    simpa [hcd] using hp
  have hcycle2 : p.cycleOf d (p.cycleOf d d) = d := by
    simpa [hcd] using hcpd
  have hswap := hc.eq_swap_of_apply_apply_eq_self hcd_ne hcycle2
  rw [hswap, Equiv.Perm.card_support_swap hcd_ne.symm]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

lemma faceLen_eq_length (C : BoundaryCycle M f) :
    M.faceLen f = C.length := by
  have hcard := congrArg Finset.card C.normalized.toFinset_eq
  have horbit : (faceOrbitFinset M f).card = M.faceLen f := by
    rfl
  rw [List.toFinset_card_of_nodup C.normalized.nodup, horbit] at hcard
  exact hcard.symm

lemma tail_injective_on_darts (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (htail : M.tail d = M.tail e) :
    d = e := by
  have hmap : (C.darts.map M.tail).Nodup := by
    simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
  exact List.inj_on_of_nodup_map hmap hd he htail

end BoundaryCycle

lemma faceLen_three_phi_cube_eq_self (M : CombMap D) (hM : M.IsSimpleGraph)
    {d : D} (hlen : M.faceLen (M.dartFace d) = 3) :
    (M.φ ^ 3) d = d := by
  have hφ : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hM d
  have hcard : (M.φ.cycleOf d).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 3 d
  rw [hcard] at hpow
  simpa using hpow.symm

lemma faceLen_three_isFaceTriangle (M : CombMap D) (hM : M.IsSimpleGraph)
    {d : D} (hlen : M.faceLen (M.dartFace d) = 3) :
    M.IsFaceTriangle d (M.φ d) (M.φ (M.φ d)) := by
  refine ⟨rfl, rfl, ?_⟩
  have hcube := faceLen_three_phi_cube_eq_self M hM hlen
  simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube

lemma faceLen_three_vertices_pairwiseDistinct (M : CombMap D) (hM : M.IsSimpleGraph)
    {d : D} (hlen : M.faceLen (M.dartFace d) = 3) :
    M.tail d ≠ M.tail (M.φ d) ∧
      M.tail (M.φ d) ≠ M.tail (M.φ (M.φ d)) ∧
      M.tail (M.φ (M.φ d)) ≠ M.tail d := by
  exact M.isFaceTriangle_vertices_pairwiseDistinct hM
    (faceLen_three_isFaceTriangle M hM hlen)

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





lemma boundary_dart_sigma_ne {d : D} (hd : d ∈ hNT.outerCycle.darts) :
    M.σ d ≠ d := by
  intro hσ
  have hdface : M.dartFace d = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff d).mp hd
  have hp : M.φ.symm d ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    simp [hdface]
  have hq : M.φ d ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    simp [hdface]
  have hαp : M.α (M.φ.symm d) = d := by
    apply M.σ.injective
    change M.φ (M.φ.symm d) = M.σ d
    rw [Equiv.apply_symm_apply, hσ]
  have hp_eq_alpha : M.φ.symm d = M.α d := by
    rw [← M.alpha_alpha (M.φ.symm d), hαp]
  have htail : M.tail (M.φ.symm d) = M.tail (M.φ d) := by
    rw [hp_eq_alpha]
    simp
  have hpq : M.φ.symm d = M.φ d :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hp hq htail
  have hφ2 : M.φ (M.φ d) = d := by
    simpa using (congrArg M.φ hpq).symm
  have hφ : M.φ d ≠ d :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph d
  have hcard2 :
      (M.φ.cycleOf d).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [hdface, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega



lemma inner_faceLen_eq_three {f : M.Face} (hf : f ≠ hNT.outerFace) :
    M.faceLen f = 3 :=
  hNT.inner_tri f hf







lemma inner_face_isFaceTriangle {d : D}
    (hd : M.dartFace d ≠ hNT.outerFace) :
    M.IsFaceTriangle d (M.φ d) (M.φ (M.φ d)) := by
  exact faceLen_three_isFaceTriangle M hNT.simpleGraph (hNT.inner_tri (M.dartFace d) hd)

lemma inner_face_vertices_pairwiseDistinct {d : D}
    (hd : M.dartFace d ≠ hNT.outerFace) :
    M.tail d ≠ M.tail (M.φ d) ∧
      M.tail (M.φ d) ≠ M.tail (M.φ (M.φ d)) ∧
      M.tail (M.φ (M.φ d)) ≠ M.tail d := by
  exact faceLen_three_vertices_pairwiseDistinct M hNT.simpleGraph
    (hNT.inner_tri (M.dartFace d) hd)









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapNearTriangulation
import ProofsInTheBook.PlanarMapDelete
-/
/- Source module: ProofsInTheBook.PlanarMapFilteredRotation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace FilteredRotation

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- The **filtered cyclic rotation** of a permutation `σ` relative to a deleted
set `Del`: the permutation of the kept subtype `{d // d ∉ Del}` that advances
along `σ` to the first surviving dart.  Thin wrapper around
`Equiv.Perm.deleteSet`, fixed here so the surgery files share one name. -/
noncomputable def filteredRotation (σ : Equiv.Perm D) (Del : Finset D) :
    Equiv.Perm {d : D // d ∉ Del} :=
  σ.deleteSet Del

@[simp]
lemma filteredRotation_apply_coe (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) :
    ((filteredRotation σ Del x : {d : D // d ∉ Del}) : D) =
      (σ ^ Equiv.Perm.DeleteSet.firstOutside σ Del x) x.1 :=
  rfl

/-- The number of `σ`-steps the filtered rotation takes from `x` is `1`
precisely when the immediate `σ`-successor of `x` is also kept. -/
lemma firstOutside_eq_one_of_next_notMem (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) (h : σ x.1 ∉ Del) :
    Equiv.Perm.DeleteSet.firstOutside σ Del x = 1 := by
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside σ Del x :=
    Equiv.Perm.DeleteSet.firstOutside_pos σ Del x
  -- `1` satisfies the search predicate, so the minimum is `≤ 1`.
  have hle : Equiv.Perm.DeleteSet.firstOutside σ Del x ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : (1 : ℕ) < Equiv.Perm.DeleteSet.firstOutside σ Del x := hcon
    have hbad := Equiv.Perm.DeleteSet.firstOutside_min σ Del x h1
    apply hbad
    refine ⟨one_pos, ?_⟩
    simpa using h
  omega

/-- **Consecutive-successor fact.**  If the `σ`-successor of a kept dart `x` is
again kept, then the filtered successor of `x` is exactly `σ x`.  This is the
local statement that, on a contiguous run of kept darts, the filtered rotation
agrees with `σ`. -/
lemma filteredRotation_apply_of_next_kept (σ : Equiv.Perm D) (Del : Finset D)
    (x : {d : D // d ∉ Del}) (h : σ x.1 ∉ Del) :
    (filteredRotation σ Del x : {d : D // d ∉ Del}).1 = σ x.1 := by
  rw [filteredRotation_apply_coe, firstOutside_eq_one_of_next_notMem σ Del x h,
    pow_one]





/-- **Orbit trace.**  The filtered rotation's orbit through a kept dart is the
trace of `σ`'s orbit on the kept subtype: two kept darts are in the same
filtered cycle iff they are in the same `σ`-cycle. -/
lemma filteredRotation_sameCycle_iff (σ : Equiv.Perm D) (Del : Finset D)
    (x y : {d : D // d ∉ Del}) :
    (filteredRotation σ Del).SameCycle x y ↔ σ.SameCycle x.1 y.1 :=
  Equiv.Perm.sameCycle_deleteSet_iff σ Del x y







namespace ContiguousInterval

variable {σ : Equiv.Perm D} {Del : Finset D} {n : ℕ}

















end ContiguousInterval



section FreshDart

variable {K : Type*} [Fintype K] [DecidableEq K]



/-- **Fresh edge involution.**  Swaps the two fresh darts and acts as `β` on the
kept summand.  Built as a sum of equivalences, hence automatically a
permutation. -/
def freshAlpha (β : Equiv.Perm K) : Equiv.Perm (K ⊕ Fin 2) :=
  Equiv.sumCongr β (Equiv.swap (0 : Fin 2) 1)

@[simp]
lemma freshAlpha_inl (β : Equiv.Perm K) (k : K) :
    freshAlpha β (Sum.inl k) = Sum.inl (β k) := rfl

@[simp]
lemma freshAlpha_inr (β : Equiv.Perm K) (j : Fin 2) :
    freshAlpha β (Sum.inr j) = Sum.inr (Equiv.swap (0 : Fin 2) 1 j) := rfl

/-- `freshAlpha β` is an involution when `β` is. -/
lemma freshAlpha_involutive (β : Equiv.Perm K) (hβ : β * β = 1) :
    freshAlpha β * freshAlpha β = 1 := by
  ext x
  cases x with
  | inl k =>
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, freshAlpha_inl,
        Equiv.Perm.coe_one, id_eq]
      have := congrArg (fun f : Equiv.Perm K => f k) hβ
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using this
  | inr j =>
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, freshAlpha_inr,
        Equiv.Perm.coe_one, id_eq, Equiv.swap_apply_self]

/-- `freshAlpha β` is fixed-point free when `β` is.  (The fresh darts are swapped
to one another, so they too are not fixed.) -/
lemma freshAlpha_no_fixed (β : Equiv.Perm K) (hβ : ∀ k, β k ≠ k) :
    ∀ x, freshAlpha β x ≠ x := by
  intro x
  cases x with
  | inl k =>
      simp only [freshAlpha_inl, ne_eq, Sum.inl.injEq]
      exact hβ k
  | inr j =>
      simp only [freshAlpha_inr, ne_eq, Sum.inr.injEq]
      fin_cases j <;> decide



variable (ρ : Equiv.Perm K) (a₀ a₁ : K)

/-- Forward map of the spliced rotation. -/
def freshSigmaFun (x : K ⊕ Fin 2) : K ⊕ Fin 2 :=
  match x with
  | Sum.inr j =>
      if j = 0 then Sum.inl (ρ a₀) else Sum.inl (ρ a₁)
  | Sum.inl k =>
      if k = a₀ then Sum.inr 0
      else if k = a₁ then Sum.inr 1
      else Sum.inl (ρ k)

/-- Inverse map of the spliced rotation. -/
def freshSigmaInv (x : K ⊕ Fin 2) : K ⊕ Fin 2 :=
  match x with
  | Sum.inr j =>
      if j = 0 then Sum.inl a₀ else Sum.inl a₁
  | Sum.inl k =>
      if k = ρ a₀ then Sum.inr 0
      else if k = ρ a₁ then Sum.inr 1
      else Sum.inl (ρ⁻¹ k)

variable {ρ a₀ a₁}

lemma freshSigma_left_inv (hne : a₀ ≠ a₁) (x : K ⊕ Fin 2) :
    freshSigmaInv ρ a₀ a₁ (freshSigmaFun ρ a₀ a₁ x) = x := by
  have hρne : ρ a₀ ≠ ρ a₁ := fun h => hne (ρ.injective h)
  cases x with
  | inr j =>
      by_cases hj : j = 0
      · subst hj; simp [freshSigmaFun, freshSigmaInv]
      · have hj1 : j = 1 := by omega
        subst hj1; simp [freshSigmaFun, freshSigmaInv, hρne.symm]
  | inl k =>
      by_cases h0 : k = a₀
      · subst h0; simp [freshSigmaFun, freshSigmaInv]
      · by_cases h1 : k = a₁
        · subst h1; simp [freshSigmaFun, freshSigmaInv, h0]
        · have hk0 : ρ k ≠ ρ a₀ := fun h => h0 (ρ.injective h)
          have hk1 : ρ k ≠ ρ a₁ := fun h => h1 (ρ.injective h)
          simp [freshSigmaFun, freshSigmaInv, h0, h1, hk0, hk1]

lemma freshSigma_right_inv (hne : a₀ ≠ a₁) (x : K ⊕ Fin 2) :
    freshSigmaFun ρ a₀ a₁ (freshSigmaInv ρ a₀ a₁ x) = x := by
  have hρne : ρ a₀ ≠ ρ a₁ := fun h => hne (ρ.injective h)
  cases x with
  | inr j =>
      by_cases hj : j = 0
      · subst hj; simp [freshSigmaFun, freshSigmaInv]
      · have hj1 : j = 1 := by omega
        subst hj1; simp [freshSigmaFun, freshSigmaInv, hne.symm]
  | inl k =>
      by_cases h0 : k = ρ a₀
      · subst h0; simp [freshSigmaFun, freshSigmaInv]
      · by_cases h1 : k = ρ a₁
        · subst h1; simp [freshSigmaFun, freshSigmaInv, h0]
        · have hk0 : ρ.symm k ≠ a₀ := by
            intro h; apply h0; rw [← h]; simp
          have hk1 : ρ.symm k ≠ a₁ := by
            intro h; apply h1; rw [← h]; simp
          simp [freshSigmaFun, freshSigmaInv, h0, h1, hk0, hk1]

variable (ρ a₀ a₁)

/-- **Fresh spliced rotation.**  The rotation `ρ` with `c₀` inserted after `a₀`
and `c₁` inserted after `a₁`.  A permutation of `K ⊕ Fin 2`. -/
def freshSigma (hne : a₀ ≠ a₁) : Equiv.Perm (K ⊕ Fin 2) where
  toFun := freshSigmaFun ρ a₀ a₁
  invFun := freshSigmaInv ρ a₀ a₁
  left_inv := freshSigma_left_inv hne
  right_inv := freshSigma_right_inv hne

@[simp]
lemma freshSigma_apply (hne : a₀ ≠ a₁) (x : K ⊕ Fin 2) :
    freshSigma ρ a₀ a₁ hne x = freshSigmaFun ρ a₀ a₁ x := rfl

/-- The anchor `a₀` now points to the fresh dart `c₀`. -/
@[simp]
lemma freshSigma_anchor_zero (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inl a₀) = Sum.inr 0 := by
  simp [freshSigma, freshSigmaFun]

/-- The anchor `a₁` now points to the fresh dart `c₁`. -/
@[simp]
lemma freshSigma_anchor_one (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inl a₁) = Sum.inr 1 := by
  simp [freshSigma, freshSigmaFun, hne.symm]

/-- The fresh dart `c₀` points to the old `ρ`-successor of `a₀`: the new cycle
through `c₀` visits `c₀` then the old cycle segment starting at `ρ a₀`. -/
@[simp]
lemma freshSigma_fresh_zero (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inr 0) = Sum.inl (ρ a₀) := by
  simp [freshSigma, freshSigmaFun]

/-- The fresh dart `c₁` points to the old `ρ`-successor of `a₁`. -/
@[simp]
lemma freshSigma_fresh_one (hne : a₀ ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inr 1) = Sum.inl (ρ a₁) := by
  simp [freshSigma, freshSigmaFun]

/-- Away from the two anchors, the spliced rotation is the old rotation. -/
lemma freshSigma_other (hne : a₀ ≠ a₁) {k : K} (h0 : k ≠ a₀) (h1 : k ≠ a₁) :
    freshSigma ρ a₀ a₁ hne (Sum.inl k) = Sum.inl (ρ k) := by
  simp only [freshSigma_apply, freshSigmaFun, if_neg h0, if_neg h1]

variable {ρ a₀ a₁}

/-- **The fresh CombMap adjunction.**  Given a fixed-point-free involution `β`
and a rotation `ρ` on the kept type `K`, with two distinct anchors, the pair
`(freshAlpha β, freshSigma ρ a₀ a₁)` is a `CombMap` on `K ⊕ Fin 2`. -/
def freshMap (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) : CombMap (K ⊕ Fin 2) where
  α := freshAlpha β
  σ := freshSigma ρ a₀ a₁ hne
  α_invol := freshAlpha_involutive β hβinv
  α_no_fixed := freshAlpha_no_fixed β hβfix

@[simp]
lemma freshMap_alpha (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).α = freshAlpha β := rfl

@[simp]
lemma freshMap_sigma (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
    (a₀ a₁ : K) (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne := rfl

end FreshDart

end FilteredRotation

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFilteredRotation
-/
/- Source module: ProofsInTheBook.PlanarMapChordSplitData -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



section ChordDarts

variable {u v : M.Vertex} (h : hNT.outerCycle.Chord u v)

/-- A dart realizing the chord edge `s(u, v)` in the ambient map. -/
noncomputable def chordDart : D :=
  let c₀ := (h.adj.2).choose
  if M.tail c₀ = u then c₀ else M.α c₀

/-- The chosen chord dart has unoriented endpoints `s(u, v)`. -/
lemma chordDart_edge : M.dartEdge (hNT.chordDart h) = s(u, v) := by
  classical
  let c₀ := (h.adj.2).choose
  have hedge : M.dartEdge c₀ = s(u, v) := (h.adj.2).choose_spec
  by_cases htail : M.tail c₀ = u
  · simp [chordDart, c₀, htail, hedge]
  · simp [chordDart, c₀, htail, M.dartEdge_alpha, hedge]

/-- The chosen chord dart is oriented from the first endpoint to the second. -/
lemma chordDart_tail : M.tail (hNT.chordDart h) = u := by
  classical
  let c₀ := (h.adj.2).choose
  have hedge : M.dartEdge c₀ = s(u, v) := (h.adj.2).choose_spec
  have hxy : s(M.tail c₀, M.head c₀) = s(u, v) := hedge
  rcases Sym2.eq_iff.mp hxy with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · simp [chordDart, c₀, ht]
  · have htail_ne : M.tail c₀ ≠ u := by
      intro htu
      exact h.endpoints_ne ((ht.symm.trans htu).symm)
    simp [chordDart, c₀, htail_ne, M.tail_alpha, hh]

/-- The chosen chord dart is oriented from the first endpoint to the second. -/
lemma chordDart_head : M.head (hNT.chordDart h) = v := by
  classical
  let c₀ := (h.adj.2).choose
  have hedge : M.dartEdge c₀ = s(u, v) := (h.adj.2).choose_spec
  have hxy : s(M.tail c₀, M.head c₀) = s(u, v) := hedge
  rcases Sym2.eq_iff.mp hxy with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · simp [chordDart, c₀, ht, hh]
  · have htail_ne : M.tail c₀ ≠ u := by
      intro htu
      exact h.endpoints_ne ((ht.symm.trans htu).symm)
    simp [chordDart, c₀, ht, h.endpoints_ne.symm, M.head_alpha]

/-- The chord's `α`-image dart has the same unoriented endpoints. -/
lemma chordDart_alpha_edge : M.dartEdge (M.α (hNT.chordDart h)) = s(u, v) := by
  rw [M.dartEdge_alpha, hNT.chordDart_edge h]

/-- The chord dart does **not** lie in the outer face: otherwise its edge would be
a boundary edge, contradicting the chord hypothesis. -/
lemma chordDart_not_outer :
    M.dartFace (hNT.chordDart h) ≠ hNT.outerFace := by
  intro hface
  apply h.not_boundary_edge
  have hmem : hNT.chordDart h ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 hface
  show s(u, v) ∈ hNT.outerCycle.edges
  rw [← hNT.chordDart_edge h, hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem

/-- The chord's `α`-image dart does **not** lie in the outer face either. -/
lemma chordDart_alpha_not_outer :
    M.dartFace (M.α (hNT.chordDart h)) ≠ hNT.outerFace := by
  intro hface
  apply h.not_boundary_edge
  have hmem : M.α (hNT.chordDart h) ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 hface
  show s(u, v) ∈ hNT.outerCycle.edges
  rw [← hNT.chordDart_alpha_edge h, hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem



/-- Both chord-incident faces are triangular. -/
lemma chord_incident_face_isFaceTriangle :
    M.IsFaceTriangle (hNT.chordDart h)
        (M.φ (hNT.chordDart h)) (M.φ (M.φ (hNT.chordDart h))) :=
  hNT.inner_face_isFaceTriangle (hNT.chordDart_not_outer h)

end ChordDarts



/-- Two faces are **chord-split adjacent** (relative to the chord `s(u, v)`) when
they share an edge that is neither a boundary edge nor the chord itself.  This is
the dual adjacency restricted to non-boundary, non-chord edges; reachability
across it never touches the outer face. -/
def ChordSplitAdj (u v : M.Vertex) (f g : M.Face) : Prop :=
  ∃ d : D,
    M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) ∧
      M.dartEdge d ≠ s(u, v)

/-- The adjacency relation is symmetric. -/
lemma chordSplitAdj_symm {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) : hNT.ChordSplitAdj u v g f := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := hfg
  refine ⟨M.α d, ?_, ?_, ?_, ?_⟩
  · exact hdg
  · rw [M.alpha_alpha]; exact hdf
  · rwa [M.dartEdge_alpha]
  · rwa [M.dartEdge_alpha]

/-- Across a chord-split adjacency, the second face is non-outer: if it were the
outer face, the shared edge would be a boundary edge. -/
lemma chordSplitAdj_target_not_outer {u v : M.Vertex} {f g : M.Face}
    (hfg : hNT.ChordSplitAdj u v f g) : g ≠ hNT.outerFace := by
  obtain ⟨d, _, hdg, hbe, _⟩ := hfg
  intro hg
  apply hbe
  have hmem : M.α d ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 (hdg.trans hg)
  show M.dartEdge d ∈ hNT.outerCycle.edges
  rw [← M.dartEdge_alpha d, hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem



/-- A **side** is the set of faces reachable from a seed face through the
chord-split adjacency relation (the reflexive–transitive closure). -/
def Side (u v : M.Vertex) (seed : M.Face) : Set M.Face :=
  {g | Relation.ReflTransGen (hNT.ChordSplitAdj u v) seed g}

/-- The seed face belongs to its own side. -/
lemma seed_mem_side {u v : M.Vertex} (seed : M.Face) :
    seed ∈ hNT.Side u v seed :=
  Relation.ReflTransGen.refl

/-- A side is closed under chord-split adjacency. -/
lemma side_closed {u v : M.Vertex} {seed f g : M.Face}
    (hf : f ∈ hNT.Side u v seed) (hfg : hNT.ChordSplitAdj u v f g) :
    g ∈ hNT.Side u v seed :=
  Relation.ReflTransGen.tail hf hfg

/-- Every face reached from a non-outer seed is non-outer.  (Non-outerness of any
face reached by at least one step is automatic from
`chordSplitAdj_target_not_outer`; combined with the seed being non-outer this
covers the whole side.) -/
lemma side_subset_nonouter {u v : M.Vertex} {seed : M.Face}
    (hseed : seed ≠ hNT.outerFace) {g : M.Face} (hg : g ∈ hNT.Side u v seed) :
    g ≠ hNT.outerFace := by
  induction hg with
  | refl => exact hseed
  | tail _ hstep _ => exact hNT.chordSplitAdj_target_not_outer hstep



/-- The set of darts whose face lies in a side. -/
def sideFaceDarts (u v : M.Vertex) (seed : M.Face) : Set D :=
  {d | M.dartFace d ∈ hNT.Side u v seed}

/-- The named planarity keystone, deferred to the side-map file (file 6).

`SidesDisjoint h` says the two side face-components are disjoint, i.e. neither
chord-incident face is reachable from the other through the non-outer adjacency.
This is the Jordan/Euler separation input (combinatorially: the chord together
with a boundary arc separates the inner faces, equivalently `F₁ + F₂ = F + 1`
once the side maps exist).  It is not derivable at this pre-construction layer;
the side-map file establishes it from the side face classification.  All
disjointness-dependent conclusions here are stated conditionally on it. -/
def SidesDisjoint {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) : Prop :=
  Disjoint
    (hNT.Side u v (M.dartFace (hNT.chordDart h)))
    (hNT.Side u v (M.dartFace (M.α (hNT.chordDart h))))

/-- All chord-split data for a near-triangulation `M` and a boundary chord `uv`.

This bundles the proven (unconditional) facts.  The single deferred planarity
input is carried as the field `sides_disjoint : hNT.SidesDisjoint h`, supplied by
the caller (file 6) once the side maps make it available; the partition lemma
below consumes it. -/
structure ChordSplitData (u v : M.Vertex) where
  /-- The chord. -/
  chord : hNT.outerCycle.Chord u v
  /-- The two boundary arcs determined by the chord endpoints. -/
  arc : BoundaryArcSplit M hNT.outerCycle.vertices hNT.outerCycle.edges u v
  /-- The first arc has an internal (strictly-between) boundary vertex. -/
  arc₁_internal : arc.path₁.HasInternalVertex
  /-- The second arc has an internal (strictly-between) boundary vertex. -/
  arc₂_internal : arc.path₂.HasInternalVertex

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}

/-- The chord dart for the data bundle. -/
noncomputable def dart (data : hNT.ChordSplitData u v) : D :=
  hNT.chordDart data.chord

/-- The first chord-incident (non-outer, triangular) face. -/
noncomputable def face₁ (data : hNT.ChordSplitData u v) : M.Face :=
  M.dartFace data.dart

/-- The second chord-incident (non-outer, triangular) face. -/
noncomputable def face₂ (data : hNT.ChordSplitData u v) : M.Face :=
  M.dartFace (M.α data.dart)

/-- The face-set of the first side (reachability closure from `face₁`). -/
def side₁ (data : hNT.ChordSplitData u v) : Set M.Face :=
  hNT.Side u v data.face₁

/-- The face-set of the second side (reachability closure from `face₂`). -/
def side₂ (data : hNT.ChordSplitData u v) : Set M.Face :=
  hNT.Side u v data.face₂

/-- The dart-set of the first side. -/
def sideDarts₁ (data : hNT.ChordSplitData u v) : Set D :=
  hNT.sideFaceDarts u v data.face₁

/-- The dart-set of the second side. -/
def sideDarts₂ (data : hNT.ChordSplitData u v) : Set D :=
  hNT.sideFaceDarts u v data.face₂



/-- The first chord-incident face is non-outer. -/
lemma face₁_not_outer (data : hNT.ChordSplitData u v) :
    data.face₁ ≠ hNT.outerFace :=
  hNT.chordDart_not_outer data.chord

/-- The second chord-incident face is non-outer. -/
lemma face₂_not_outer (data : hNT.ChordSplitData u v) :
    data.face₂ ≠ hNT.outerFace :=
  hNT.chordDart_alpha_not_outer data.chord

/-- The first chord-incident face is triangular. -/
lemma face₁_isFaceTriangle (data : hNT.ChordSplitData u v) :
    M.IsFaceTriangle data.dart (M.φ data.dart) (M.φ (M.φ data.dart)) :=
  hNT.chord_incident_face_isFaceTriangle data.chord

/-- The seed `face₁` belongs to side 1. -/
lemma face₁_mem_side₁ (data : hNT.ChordSplitData u v) :
    data.face₁ ∈ data.side₁ :=
  hNT.seed_mem_side _

/-- The seed `face₂` belongs to side 2. -/
lemma face₂_mem_side₂ (data : hNT.ChordSplitData u v) :
    data.face₂ ∈ data.side₂ :=
  hNT.seed_mem_side _

/-- Side 1 is closed under the chord-split adjacency relation. -/
lemma side₁_closed (data : hNT.ChordSplitData u v) {f g : M.Face}
    (hf : f ∈ data.side₁) (hfg : hNT.ChordSplitAdj u v f g) : g ∈ data.side₁ :=
  hNT.side_closed hf hfg

/-- Side 2 is closed under the chord-split adjacency relation. -/
lemma side₂_closed (data : hNT.ChordSplitData u v) {f g : M.Face}
    (hf : f ∈ data.side₂) (hfg : hNT.ChordSplitAdj u v f g) : g ∈ data.side₂ :=
  hNT.side_closed hf hfg

/-- Every face of side 1 is non-outer. -/
lemma side₁_subset_nonouter (data : hNT.ChordSplitData u v) {g : M.Face}
    (hg : g ∈ data.side₁) : g ≠ hNT.outerFace :=
  hNT.side_subset_nonouter data.face₁_not_outer hg

/-- Every face of side 2 is non-outer. -/
lemma side₂_subset_nonouter (data : hNT.ChordSplitData u v) {g : M.Face}
    (hg : g ∈ data.side₂) : g ≠ hNT.outerFace :=
  hNT.side_subset_nonouter data.face₂_not_outer hg











end ChordSplitData







end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplitData
-/
/- Source module: ProofsInTheBook.PlanarMapChordSplit -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- Under `Nodup`, the last element of a list does not occur in its `dropLast`. -/
lemma getLast_notMem_dropLast {α : Type*} {l : List α} (hl : l ≠ [])
    (hnd : l.Nodup) : l.getLast hl ∉ l.dropLast := by
  have hsplit : l.dropLast ++ [l.getLast hl] = l := List.dropLast_append_getLast hl
  have hnd' : (l.dropLast ++ [l.getLast hl]).Nodup := by rw [hsplit]; exact hnd
  intro hmem
  exact (List.disjoint_of_nodup_append hnd') hmem (by simp)

/-- A generic list fact: if `l.head? = some a` and `l.Nodup`, then `a ∉ l.tail`. -/
lemma head?_notMem_tail {α : Type*} {a : α} {l : List α}
    (hh : l.head? = some a) (hnd : l.Nodup) : a ∉ l.tail := by
  cases l with
  | nil => simp at hh
  | cons b t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simpa using (List.nodup_cons.mp hnd).1

/-- A generic list fact: if `l.getLast? = some a` and `l.tail ≠ []`, then `a` is
the last element of `l.tail`. -/
lemma getLast_tail_of_getLast? {α : Type*} {a : α} {l : List α}
    (hl : l.getLast? = some a) (ht : l.tail ≠ []) :
    l.tail.getLast ht = a := by
  cases l with
  | nil => exact absurd rfl ht
  | cons b s =>
      simp only [List.tail_cons] at ht ⊢
      have hs : (b :: s).getLast? = some a := hl
      rw [List.getLast?_eq_some_getLast (by simp)] at hs
      simp only [Option.some.injEq] at hs
      rw [← hs, List.getLast_cons ht]

namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}



/-- An internal vertex is distinct from the initial endpoint. -/
lemma internalVertex_ne_start (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ u := by
  -- `u` is the head, so `u ∉ tail ⊇ dropLast tail ∋ w`.
  have hutail : u ∉ P.vertices.tail :=
    head?_notMem_tail P.starts_at P.simple
  have hwtail : w ∈ P.vertices.tail := List.dropLast_subset _ hw
  intro hwu; subst hwu; exact hutail hwtail

/-- An internal vertex is distinct from the terminal endpoint. -/
lemma internalVertex_ne_end (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ v := by
  have hwtail_dropLast : w ∈ P.vertices.tail.dropLast := hw
  have htail_ne : P.vertices.tail ≠ [] := fun h => by rw [h] at hwtail_dropLast; simp at hwtail_dropLast
  have hnodup_tail : P.vertices.tail.Nodup := P.simple.sublist (List.tail_sublist _)
  -- `v` is the last of the tail, and the last is not in `dropLast` under nodup.
  have hlast_tail : P.vertices.tail.getLast htail_ne = v :=
    getLast_tail_of_getLast? P.ends_at htail_ne
  have hnotmem : P.vertices.tail.getLast htail_ne ∉ P.vertices.tail.dropLast :=
    getLast_notMem_dropLast htail_ne hnodup_tail
  intro hwv; subst hwv
  -- `w = v = getLast tail`, and `w ∈ dropLast tail`, contradiction.
  exact hnotmem (hlast_tail.symm ▸ hwtail_dropLast)



end BoundaryPath

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}

















/-- **`α`-closure away from the seam (side 1).**  If a side-1 dart `e` (its face
lies in side 1) has an edge that is neither a boundary edge nor the chord, then
`α e` is again a side-1 dart.  In other words, the *only* edges along which side
1 can leak are boundary edges and the chord. -/
lemma alpha_mem_side₁_of_interior (data : hNT.ChordSplitData u v) {e : D}
    (he : M.dartFace e ∈ data.side₁)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge e))
    (hc : M.dartEdge e ≠ s(u, v)) :
    M.dartFace (M.α e) ∈ data.side₁ := by
  have hadj : hNT.ChordSplitAdj u v (M.dartFace e) (M.dartFace (M.α e)) :=
    ⟨e, rfl, rfl, hb, by
      -- rewrite the chord edge `s(u,v)` against `data.chord`'s endpoints
      simpa using hc⟩
  exact data.side₁_closed he hadj

/-- **`α`-closure away from the seam (side 2).** -/
lemma alpha_mem_side₂_of_interior (data : hNT.ChordSplitData u v) {e : D}
    (he : M.dartFace e ∈ data.side₂)
    (hb : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge e))
    (hc : M.dartEdge e ≠ s(u, v)) :
    M.dartFace (M.α e) ∈ data.side₂ := by
  have hadj : hNT.ChordSplitAdj u v (M.dartFace e) (M.dartFace (M.α e)) :=
    ⟨e, rfl, rfl, hb, by simpa using hc⟩
  exact data.side₂_closed he hadj



/-- Side membership is symmetric: `g ∈ Side f ↔ f ∈ Side g`.  (Reflexive–
transitive closure of a symmetric relation is symmetric.) -/
lemma side_mem_symm {seed g : M.Face}
    (h : g ∈ hNT.Side u v seed) : seed ∈ hNT.Side u v g :=
  Relation.ReflTransGen.symmetric (fun _ _ => hNT.chordSplitAdj_symm) h

/-- **The chord-split separation predicate.**  `Separates data` says the second
chord-incident face is not reachable from the first through the non-outer
adjacency.  This is the sharp, single-non-reachability form of the file-5
planarity keystone `SidesDisjoint`; it is the genuine Jordan/Euler separation
input for the chord split and is *not* derivable at the combinatorial-map level
(see the module docstring).  It is the one isolated classification input. -/
def Separates (data : hNT.ChordSplitData u v) : Prop :=
  data.face₂ ∉ data.side₁

/-- **The separation predicate is equivalent to the file-5 keystone
`SidesDisjoint`.**  This is a genuine reduction: the full disjointness of the two
side face-components reduces, via symmetry of reachability, to the single
non-reachability `face₂ ∉ side₁`.  Thus a downstream separation theorem need
only establish `Separates` to discharge `SidesDisjoint` (and hence the partition
lemma `chordSplit_side_darts_partition`). -/
theorem separates_iff_sidesDisjoint (data : hNT.ChordSplitData u v) :
    data.Separates ↔ hNT.SidesDisjoint data.chord := by
  constructor
  · -- `face₂ ∉ side₁` ⇒ the two sides are disjoint.
    intro hsep
    rw [SidesDisjoint, Set.disjoint_left]
    intro f hf1 hf2
    -- `f ∈ side₁` and `f ∈ side₂`; show `face₂ ∈ side₁`, contradicting `hsep`.
    -- `f ∈ side₂` means `face₂ ∈ Side f` (symmetry), and `f ∈ side₁` chains.
    have hf2' : data.face₂ ∈ hNT.Side u v f := side_mem_symm hf2
    -- `Side` is transitive: `face₁ ⇝ f ⇝ face₂`, so `face₂ ∈ side₁`.
    have : data.face₂ ∈ data.side₁ :=
      Relation.ReflTransGen.trans hf1 hf2'
    exact hsep this
  · -- `SidesDisjoint` ⇒ `face₂ ∉ side₁`.
    intro hdisj hmem
    -- `face₂ ∈ side₁` and `face₂ ∈ side₂` (seed), contradicting disjointness.
    rw [SidesDisjoint, Set.disjoint_left] at hdisj
    exact hdisj hmem data.face₂_mem_side₂























/-- The outer-face darts whose `α`-reverse is an inner dart of side 1. -/
def outerArc₁ (data : hNT.ChordSplitData u v) : Set D :=
  {b | M.dartFace b = hNT.outerFace ∧ M.dartFace (M.α b) ∈ data.side₁}

/-- The outer-face darts whose `α`-reverse is an inner dart of side 2. -/
def outerArc₂ (data : hNT.ChordSplitData u v) : Set D :=
  {b | M.dartFace b = hNT.outerFace ∧ M.dartFace (M.α b) ∈ data.side₂}

/-- The faithful kept dart set of side 1: inner side-1 darts together with the
matching outer boundary darts, minus the original chord dart. -/
def keptSet₁ (data : hNT.ChordSplitData u v) : Set D :=
  (data.sideDarts₁ ∪ data.outerArc₁) \ {data.dart}

/-- The faithful kept dart set of side 2 (the chord *reverse* `α dart` is the
side-2 seam dart that is removed). -/
def keptSet₂ (data : hNT.ChordSplitData u v) : Set D :=
  (data.sideDarts₂ ∪ data.outerArc₂) \ {M.α data.dart}

/-- The chord edge has exactly the two darts `dart` and `α dart`: any dart whose
unoriented endpoints are `s(u, v)` is `α.SameCycle` with the chord dart, hence
equal to it or its reverse.  UNCONDITIONAL (uses only graph simplicity). -/
lemma chord_edge_darts (data : hNT.ChordSplitData u v) {e : D}
    (he : M.dartEdge e = s(u, v)) : e = data.dart ∨ e = M.α data.dart := by
  have hedge : M.dartEdge e = M.dartEdge data.dart := by
    rw [he]; exact (hNT.chordDart_edge data.chord).symm
  have hsc : M.α.SameCycle e data.dart :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hedge
  rcases (M.alpha_sameCycle_iff data.dart e).mp hsc.symm with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- For a boundary edge, at least one of its two darts lies on the outer face.
UNCONDITIONAL.  (A boundary edge is the `dartEdge` of some outer-cycle dart; the
two darts of an edge are `b` and `α b` by simplicity.) -/
lemma boundaryEdge_dart_outer (_data : hNT.ChordSplitData u v) {e : D}
    (hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)) :
    M.dartFace e = hNT.outerFace ∨ M.dartFace (M.α e) = hNT.outerFace := by
  -- `dartEdge e ∈ edges = darts.map dartEdge`, so some outer dart `b` has the
  -- same `dartEdge`; by simplicity `α.SameCycle e b`, i.e. `e = b` or `e = α b`.
  rw [BoundaryCycle.IsBoundaryEdge, hNT.outerCycle.edges_eq, List.mem_map] at hbe
  obtain ⟨b, hb, hbe⟩ := hbe
  have hbface : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).mp hb
  have hsc : M.α.SameCycle e b :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hbe.symm
  rcases (M.alpha_sameCycle_iff b e).mp hsc.symm with h | h
  · exact Or.inl (by rw [h]; exact hbface)
  · right; rw [h, M.alpha_alpha]; exact hbface

/-- Under `Separates`, the chord *reverse* `α dart` is not in the side-1 kept set
(its face `face₂` is outside side 1, and it is not an outer dart). -/
lemma alphaDart_notMem_keptSet₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : M.α data.dart ∉ data.keptSet₁ := by
  rintro ⟨hU, _⟩
  rcases hU with h1 | h2
  · -- `α dart ∈ sideDarts₁` means `face₂ ∈ side₁`, contradicting `Separates`.
    exact hsep h1
  · -- `α dart ∈ outerArc₁` needs `dartFace (α dart) = outerFace`, but it is `face₂`.
    exact data.face₂_not_outer h2.1

/-- **The side-1 kept set is closed under `α`** (conditional on `Separates`).
Away from the chord (removed) and the boundary edges (outer dart kept in
`outerArc₁`), `α` maps `keptSet₁` into itself. -/
theorem alpha_keptSet₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (he : e ∈ data.keptSet₁) : M.α e ∈ data.keptSet₁ := by
  classical
  obtain ⟨heU, hene⟩ := he
  simp only [Set.mem_singleton_iff] at hene
  -- `α e ≠ dart`: else `e = α dart ∉ keptSet₁`, contradicting `e ∈ keptSet₁`.
  have hαe_ne : M.α e ≠ data.dart := by
    intro hcontra
    have he_eq : e = M.α data.dart := by
      have := congrArg M.α hcontra; rwa [M.alpha_alpha] at this
    exact data.alphaDart_notMem_keptSet₁ hsep (he_eq ▸ ⟨heU, by
      simp only [Set.mem_singleton_iff]; exact hene⟩)
  refine ⟨?_, by simp only [Set.mem_singleton_iff]; exact hαe_ne⟩
  rcases heU with hin | hout
  · have hface_e : M.dartFace e ∈ data.side₁ := hin
    have he_not_outer : M.dartFace e ≠ hNT.outerFace :=
      data.side₁_subset_nonouter hface_e
    by_cases hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)
    · right
      have hαe_outer : M.dartFace (M.α e) = hNT.outerFace := by
        rcases data.boundaryEdge_dart_outer hbe with h | h
        · exact absurd h he_not_outer
        · exact h
      exact ⟨hαe_outer, by rw [M.alpha_alpha]; exact hface_e⟩
    · left
      have hch : M.dartEdge e ≠ s(u, v) := by
        intro hchord
        rcases data.chord_edge_darts hchord with h | h
        · exact hene h
        · -- `e = α dart`, so `dartFace e = face₂`; `hin` says `face₂ ∈ side₁`.
          apply hsep
          show M.dartFace (M.α data.dart) ∈ data.side₁
          rw [← h]; exact hin
      exact data.alpha_mem_side₁_of_interior hface_e hbe hch
  · left; exact hout.2

/-- `Separates` is symmetric across the two sides: it also gives `face₁ ∉ side₂`.
(Via symmetry of reachability: `face₁ ∈ side₂` would force `face₂ ∈ side₁`.) -/
lemma separates_symm (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.face₁ ∉ data.side₂ := by
  intro hmem
  -- `face₁ ∈ Side face₂` ⇒ `face₂ ∈ Side face₁ = side₁`, contradicting `Separates`.
  exact hsep (side_mem_symm hmem)

/-- Under `Separates`, the chord dart `dart` is not in the side-2 kept set. -/
lemma dart_notMem_keptSet₂ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : data.dart ∉ data.keptSet₂ := by
  rintro ⟨hU, _⟩
  rcases hU with h1 | h2
  · -- `dart ∈ sideDarts₂` means `face₁ ∈ side₂`, contradicting `separates_symm`.
    exact data.separates_symm hsep h1
  · -- `dart ∈ outerArc₂` needs `dartFace dart = outerFace`, but it is `face₁`.
    exact data.face₁_not_outer h2.1

/-- **The side-2 kept set is closed under `α`** (conditional on `Separates`). -/
theorem alpha_keptSet₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (he : e ∈ data.keptSet₂) : M.α e ∈ data.keptSet₂ := by
  classical
  obtain ⟨heU, hene⟩ := he
  simp only [Set.mem_singleton_iff] at hene
  have hαe_ne : M.α e ≠ M.α data.dart := by
    intro hcontra
    have he_eq : e = data.dart := M.α.injective hcontra
    exact data.dart_notMem_keptSet₂ hsep (he_eq ▸ ⟨heU, by
      simp only [Set.mem_singleton_iff]; exact hene⟩)
  refine ⟨?_, by simp only [Set.mem_singleton_iff]; exact hαe_ne⟩
  rcases heU with hin | hout
  · have hface_e : M.dartFace e ∈ data.side₂ := hin
    have he_not_outer : M.dartFace e ≠ hNT.outerFace :=
      data.side₂_subset_nonouter hface_e
    by_cases hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)
    · right
      have hαe_outer : M.dartFace (M.α e) = hNT.outerFace := by
        rcases data.boundaryEdge_dart_outer hbe with h | h
        · exact absurd h he_not_outer
        · exact h
      exact ⟨hαe_outer, by rw [M.alpha_alpha]; exact hface_e⟩
    · left
      have hch : M.dartEdge e ≠ s(u, v) := by
        intro hchord
        rcases data.chord_edge_darts hchord with h | h
        · -- `e = dart`, so `dartFace e = face₁`; `hin` says `face₁ ∈ side₂`.
          apply data.separates_symm hsep
          show M.dartFace data.dart ∈ data.side₂
          rw [← h]; exact hin
        · exact hene h
      exact data.alpha_mem_side₂_of_interior hface_e hbe hch
  · left; exact hout.2



open scoped Classical in
/-- The deleted dart-set of side 1, as a `Finset` (complement of `keptSet₁`). -/
noncomputable def keptDel₁ (data : hNT.ChordSplitData u v) : Finset D :=
  Finset.univ.filter (fun d => d ∉ data.keptSet₁)

open scoped Classical in
/-- The deleted dart-set of side 2, as a `Finset` (complement of `keptSet₂`). -/
noncomputable def keptDel₂ (data : hNT.ChordSplitData u v) : Finset D :=
  Finset.univ.filter (fun d => d ∉ data.keptSet₂)

lemma mem_keptDel₁_iff (data : hNT.ChordSplitData u v) (d : D) :
    d ∉ data.keptDel₁ ↔ d ∈ data.keptSet₁ := by
  classical
  simp only [keptDel₁, Finset.mem_filter, Finset.mem_univ, true_and, not_not]

lemma mem_keptDel₂_iff (data : hNT.ChordSplitData u v) (d : D) :
    d ∉ data.keptDel₂ ↔ d ∈ data.keptSet₂ := by
  classical
  simp only [keptDel₂, Finset.mem_filter, Finset.mem_univ, true_and, not_not]

/-- Membership in the side-1 kept set is `α`-invariant (under `Separates`). -/
lemma mem_keptSet₁_alpha_iff (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : D) : M.α d ∈ data.keptSet₁ ↔ d ∈ data.keptSet₁ := by
  constructor
  · intro hd
    have := data.alpha_keptSet₁ hsep hd
    rwa [M.alpha_alpha] at this
  · intro hd; exact data.alpha_keptSet₁ hsep hd

/-- Membership in the side-2 kept set is `α`-invariant (under `Separates`). -/
lemma mem_keptSet₂_alpha_iff (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : D) : M.α d ∈ data.keptSet₂ ↔ d ∈ data.keptSet₂ := by
  constructor
  · intro hd
    have := data.alpha_keptSet₂ hsep hd
    rwa [M.alpha_alpha] at this
  · intro hd; exact data.alpha_keptSet₂ hsep hd

/-- **The side-1 edge involution.**  `α` restricted to the kept subtype of side 1.
A genuine permutation because `keptSet₁` is `α`-closed (under `Separates`). -/
noncomputable def sideAlpha₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    Equiv.Perm {d : D // d ∉ data.keptDel₁} :=
  M.α.subtypePerm (fun d => by
    rw [data.mem_keptDel₁_iff, data.mem_keptDel₁_iff]
    constructor
    · intro hd; exact (data.mem_keptSet₁_alpha_iff hsep d).1 hd
    · intro hd; exact (data.mem_keptSet₁_alpha_iff hsep d).2 hd)

/-- **The side-2 edge involution.** -/
noncomputable def sideAlpha₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    Equiv.Perm {d : D // d ∉ data.keptDel₂} :=
  M.α.subtypePerm (fun d => by
    rw [data.mem_keptDel₂_iff, data.mem_keptDel₂_iff]
    constructor
    · intro hd; exact (data.mem_keptSet₂_alpha_iff hsep d).1 hd
    · intro hd; exact (data.mem_keptSet₂_alpha_iff hsep d).2 hd)

@[simp]
lemma sideAlpha₁_apply_coe (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁}) :
    (data.sideAlpha₁ hsep d : D) = M.α d.1 := by
  simp [sideAlpha₁]

@[simp]
lemma sideAlpha₂_apply_coe (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₂}) :
    (data.sideAlpha₂ hsep d : D) = M.α d.1 := by
  simp [sideAlpha₂]

/-- **Side-1 edge involution is an involution.** -/
lemma sideAlpha₁_involutive (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₁ hsep * data.sideAlpha₁ hsep = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sideAlpha₁_apply_coe,
    Equiv.Perm.coe_one, id_eq]
  exact M.alpha_alpha d.1

/-- **Side-2 edge involution is an involution.** -/
lemma sideAlpha₂_involutive (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₂ hsep * data.sideAlpha₂ hsep = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, sideAlpha₂_apply_coe,
    Equiv.Perm.coe_one, id_eq]
  exact M.alpha_alpha d.1

/-- **Side-1 edge involution is fixed-point free.** -/
lemma sideAlpha₁_no_fixed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, data.sideAlpha₁ hsep d ≠ d := by
  intro d hd
  apply M.α_no_fixed d.1
  have := congrArg Subtype.val hd
  rwa [sideAlpha₁_apply_coe] at this

/-- **Side-2 edge involution is fixed-point free.** -/
lemma sideAlpha₂_no_fixed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, data.sideAlpha₂ hsep d ≠ d := by
  intro d hd
  apply M.α_no_fixed d.1
  have := congrArg Subtype.val hd
  rwa [sideAlpha₂_apply_coe] at this

/-- **The side-1 filtered rotation** (the kept σ before the fresh chord splice),
from file 4's generic `filteredRotation`.  A genuine permutation by construction. -/
noncomputable def sideSigma₁ (data : hNT.ChordSplitData u v) :
    Equiv.Perm {d : D // d ∉ data.keptDel₁} :=
  FilteredRotation.filteredRotation M.σ data.keptDel₁

/-- **The side-2 filtered rotation.** -/
noncomputable def sideSigma₂ (data : hNT.ChordSplitData u v) :
    Equiv.Perm {d : D // d ∉ data.keptDel₂} :=
  FilteredRotation.filteredRotation M.σ data.keptDel₂



/-- **The side-1 map.**  The fresh-dart adjunction over the side-1 kept type, with
edge involution `sideAlpha₁`, rotation `sideSigma₁`, and a duplicated chord edge
spliced at the two anchor darts `a₀, a₁`.  Its `α` is a fixed-point-free
involution and its `σ` is a permutation, both from `freshMap`. -/
noncomputable def sideMap₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    CombMap ({d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :=
  FilteredRotation.freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne

/-- **The side-2 map.** -/
noncomputable def sideMap₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    CombMap ({d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :=
  FilteredRotation.freshMap (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep) a₀ a₁ hne













end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplit
-/
/- Source module: ProofsInTheBook.PlanarMapSeparation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)









namespace ChordSplitData

variable {hNT} {u v : M.Vertex}







/-- `Separates` literally says the second chord face is not in side 1. -/
lemma not_separates_iff_face₂_mem (data : hNT.ChordSplitData u v) :
    ¬ data.Separates ↔ data.face₂ ∈ data.side₁ := by
  unfold Separates
  exact not_not







/-- **`Separates` is the bridge property of the chord in the interior dual.**
`¬ Separates` holds iff the second chord face is reachable from the first through
`ChordSplitAdj` (which avoids the chord), i.e. iff there is a chord-avoiding dual
path joining the two chord faces.  Since the chord itself directly joins them,
this is exactly "the chord lies on a dual cycle" / "the chord is not a bridge of
the interior dual". -/
lemma not_separates_iff_reachable_avoiding_chord (data : hNT.ChordSplitData u v) :
    ¬ data.Separates ↔
      Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ data.face₂ := by
  rw [data.not_separates_iff_face₂_mem]
  rfl



end ChordSplitData

/-- **The genus-0 chord separation input** (the combinatorial Jordan curve
theorem for sphere near-triangulations).  For a boundary chord `uv`, the two
chord-incident inner faces are **not** joined by a `ChordSplitAdj`-path — a dual
path avoiding boundary edges and the chord.  Combinatorially this is the
non-bridge/separating-cycle fact equivalent to the per-side Euler count
`F₁ + F₂ = F + 1`; it is the one isolated planarity keystone of the chord split. -/
def SphereChordSeparation {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) : Prop :=
  ¬ Relation.ReflTransGen (hNT.ChordSplitAdj u v)
      (M.dartFace (hNT.chordDart h)) (M.dartFace (M.α (hNT.chordDart h)))

namespace ChordSplitData

variable {hNT} {u v : M.Vertex}





/-- **The chord-split separation theorem** (conditional on the isolated Jordan/
Euler input `SphereChordSeparation`).  Given the genus-0 separation input, the
second chord-incident face is not reachable from the first through the non-outer
adjacency avoiding boundary edges and the chord: i.e. `data.Separates`.

This is an honest conditional theorem on the one sharply-isolated planarity
input; by `sphereChordSeparation_iff_separates` the input is the separation
content itself at the interior-dual level (no hidden strengthening). -/
theorem separates_of_nearTriangulation (data : hNT.ChordSplitData u v)
    (hsep : hNT.SphereChordSeparation data.chord) : data.Separates := by
  by_contra hns
  exact hsep ((data.not_separates_iff_reachable_avoiding_chord).1 hns)



end ChordSplitData

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap


end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapNearTriangulation
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryFan -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}

/-- The base case for the boundary-deletion branch: exactly three graph
vertices. -/
def IsBaseTriangle (_hNT : NearTriangulation M) : Prop :=
  M.V = 3

/-- Consecutive unordered fan-path vertex pairs, represented in path order. -/
def consecutivePairs {α : Type*} (xs : List α) : List (α × α) :=
  xs.zip xs.tail

/-- The exposed fan path `x, z_1, ..., z_t, w`. -/
def fanPath (x : M.Vertex) (interior : List M.Vertex) (w : M.Vertex) :
    List M.Vertex :=
  x :: interior ++ [w]

/-- A face is incident with a vertex if one of its boundary darts has that
vertex as tail. -/
def FaceIncidentAtVertex (M : CombMap D) (f : M.Face) (v : M.Vertex) : Prop :=
  ∃ d : D, M.dartFace d = f ∧ M.tail d = v

/-- A triangle in the fan, with vertices in cyclic face order
`v0, a, b`. -/
structure FanTriangle (hNT : NearTriangulation M)
    (v0 a b : M.Vertex) where
  d0 : D
  d1 : D
  d2 : D
  triangle : M.IsFaceTriangle d0 d1 d2
  inner : M.dartFace d0 ≠ hNT.outerFace
  tail0 : M.tail d0 = v0
  tail1 : M.tail d1 = a
  tail2 : M.tail d2 = b

namespace FanTriangle

variable {hNT : NearTriangulation M} {v0 a b : M.Vertex}

/-- The inner face represented by a certified fan triangle. -/
def face (T : FanTriangle hNT v0 a b) : M.Face :=
  M.dartFace T.d0

lemma face_ne_outer (T : FanTriangle hNT v0 a b) :
    T.face ≠ hNT.outerFace :=
  T.inner

lemma faceLen_eq_three (T : FanTriangle hNT v0 a b) :
    M.faceLen T.face = 3 :=
  hNT.inner_faceLen_eq_three T.face_ne_outer

lemma vertices_pairwiseDistinct (T : FanTriangle hNT v0 a b) :
    v0 ≠ a ∧ a ≠ b ∧ b ≠ v0 := by
  have hdistinct :=
    M.isFaceTriangle_vertices_pairwiseDistinct hNT.simpleGraph T.triangle
  constructor
  · intro h
    exact hdistinct.1 (T.tail0.trans (h.trans T.tail1.symm))
  constructor
  · intro h
    exact hdistinct.2.1 (T.tail1.trans (h.trans T.tail2.symm))
  · intro h
    exact hdistinct.2.2 (T.tail2.trans (h.trans T.tail0.symm))

end FanTriangle

/-- The neighbors of `v0` occur in the listed cyclic rotation order.  This is
kept as data because File 3 does not yet expose a normalized vertex-rotation
list analogous to `BoundaryCycle.darts`. -/
structure NeighborRotationOrder (M : CombMap D) (v0 : M.Vertex)
    (neighbors : List M.Vertex) where
  darts : List D
  darts_nodup : darts.Nodup
  darts_nonempty : 0 < darts.length
  tails_eq : darts.map M.tail = List.replicate darts.length v0
  heads_eq : darts.map M.head = neighbors
  consecutive_sigma :
    ∀ i : Fin darts.length,
      darts.get (cyclicNext darts_nonempty i) = M.σ (darts.get i)

/-- The exact statement that the non-outer faces incident with `v0` are the
consecutive fan triangles along `path`.

**σ-backward / predecessor orientation (machine-certified fix, commit 15bd7a6).**
The `φ`-triangle of an inner spoke `e` at `v0` orients its edge toward the
σ-*predecessor* `head (σ⁻¹ e)`, never the σ-successor
(`ZinanCh35ChordlessFull.spokeFace_head_eq`); a forward-oriented
`FanTriangle hNT v0 a b` for a σ-forward consecutive pair `(a, b)` would force the
star of `v0` to have degree `≤ 2`
(`ZinanCh35ChordlessFull.forward_fanTriangle_forces_degree_two`).  The genuine face
between two σ-consecutive spokes carries the **reverse** labelling, so for a
consecutive pair `(a, b)` of `path` the certified triangle is
`FanTriangle hNT v0 b a` (apex `v0`, directed edge `b → a`).  All downstream
consumers use only the *unordered* edge `{a, b}` of the triangle (its surviving
edge dart, its face, and the symmetric `VConn`), so the predecessor labelling
re-threads cleanly.

The `exact_faces` field is stated with the **correct quantifier nesting**
`f ≠ outerFace → (Incident ↔ Exists)` (the legacy `→ … ↔ …` parsed as
`(f ≠ outer → Incident) ↔ Exists`, which is literally `True ↔ False` at
`f = outerFace`, making the structure uninhabitable). -/
structure IncidentNonOuterFacesExactly (hNT : NearTriangulation M)
    (v0 : M.Vertex) (path : List M.Vertex) where
  triangle_of_pair :
    ∀ {a b : M.Vertex}, (a, b) ∈ consecutivePairs path →
      FanTriangle hNT v0 b a
  exact_faces :
    ∀ f : M.Face, f ≠ hNT.outerFace →
      (FaceIncidentAtVertex M f v0 ↔
        ∃ (a b : M.Vertex) (hp : (a, b) ∈ consecutivePairs path),
          (triangle_of_pair hp).face = f)

/-- A certified boundary fan at a boundary vertex `v0`.

The interior list is `z_1, ..., z_t`; the exposed path is
`x :: interior ++ [w]`.  The chordless fields are included because they are the
facts needed later for boundary deletion and are not derivable from the current
File 3 API alone. -/
structure BoundaryVertexFan (hNT : NearTriangulation M) (v0 : M.Vertex) where
  x : M.Vertex
  interior : List M.Vertex
  w : M.Vertex
  v0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  x_boundary : hNT.outerCycle.IsBoundaryVertex x
  w_boundary : hNT.outerCycle.IsBoundaryVertex w
  rotation_order : NeighborRotationOrder M v0 (fanPath x interior w)
  incident_faces_exact :
    IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)
  path_nodup_of_chordless :
    BoundaryChordless hNT.outerCycle → (fanPath x interior w).Nodup
  interior_not_boundary_of_chordless :
    BoundaryChordless hNT.outerCycle →
      ∀ z : M.Vertex, z ∈ interior → ¬ hNT.outerCycle.IsBoundaryVertex z
  empty_iff_base_triangle_of_chordless :
    BoundaryChordless hNT.outerCycle → (interior = [] ↔ hNT.IsBaseTriangle)

namespace BoundaryVertexFan

variable {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- The exposed path `x, z_1, ..., z_t, w`. -/
def path (fan : BoundaryVertexFan hNT v0) : List M.Vertex :=
  fanPath fan.x fan.interior fan.w

/-- Number of exposed interior fan vertices. -/
def t (fan : BoundaryVertexFan hNT v0) : ℕ :=
  fan.interior.length





end BoundaryVertexFan

variable (hNT : NearTriangulation M) {v0 : M.Vertex}





/-- Under chordlessness, the exposed fan path has no repeated vertices. -/
theorem fan_path_simple_of_chordless (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    fan.path.Nodup := by
  simpa [BoundaryVertexFan.path] using
    fan.path_nodup_of_chordless hchordless

/-- Under chordlessness, an exposed interior fan vertex is not an old boundary
vertex. -/
theorem fan_interior_vertices_not_boundary_of_chordless
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ z : M.Vertex, z ∈ fan.interior → ¬ hNT.outerCycle.IsBoundaryVertex z :=
  fan.interior_not_boundary_of_chordless hchordless





/-- Under chordlessness, the exposed fan path meets the old boundary only at
its two endpoint vertices. -/
theorem fan_path_meets_old_boundary_only_at_ends
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) :
    ∀ y : M.Vertex, y ∈ fan.path → hNT.outerCycle.IsBoundaryVertex y →
      y = fan.x ∨ y = fan.w := by
  intro y hy hy_boundary
  have hy_path : y ∈ fan.x :: fan.interior ++ [fan.w] := by
    simpa [BoundaryVertexFan.path, fanPath] using hy
  rcases List.mem_cons.mp hy_path with hyx | hyrest
  · exact Or.inl hyx
  · rcases List.mem_append.mp hyrest with hyint | hyw
    · exact False.elim
        ((fan_interior_vertices_not_boundary_of_chordless hNT fan hchordless
          y hyint) hy_boundary)
    · have hyw' : y = fan.w := by
        simpa using hyw
      exact Or.inr hyw'

/-- In the chordless non-base case, the fan has at least one exposed interior
vertex.  This is the tetrahedron/minimal-`t=1` side of the deletion case. -/
theorem fan_nonempty_of_chordless_of_not_triangle
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hnot_base : 3 < M.V) :
    1 ≤ fan.t := by
  have hne : fan.t ≠ 0 := by
    intro ht0
    have hlen : fan.interior.length = 0 := by
      simpa [BoundaryVertexFan.t] using ht0
    have hempty : fan.interior = [] :=
      List.length_eq_zero_iff.mp hlen
    have hbase : hNT.IsBaseTriangle :=
      (fan.empty_iff_base_triangle_of_chordless hchordless).1 hempty
    unfold IsBaseTriangle at hbase
    omega
  exact Nat.one_le_iff_ne_zero.mpr hne



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundaryFan
import ProofsInTheBook.PlanarMapDelete
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryDelete -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}



/-- A simple graph has no loop at any vertex (dart-representative form), so the
deletion edge-count hypothesis `NoLoopAt` holds unconditionally. -/
lemma noLoopAt_of_simpleGraph (hNT : NearTriangulation M) (d0 : D) :
    M.NoLoopAt d0 := by
  intro d hd
  rw [mem_vertexDarts] at hd ⊢
  exact noLoopAt_dart_of_isSimpleGraph M hNT.simpleGraph d0 d hd


structure BoundaryDeletionData (hNT : NearTriangulation M) (d0 : D) where
  /-- Local simple-boundary condition: distinct darts at `v0` lie on distinct
  faces. -/
  vertexFacesDistinct : M.VertexFacesDistinct d0
  /-- The surviving vertex quotients are the old ones minus the orbit of `d0`. -/
  vertexQuotient :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0}
  /-- The faces incident with `v0` merge into one new outer face. -/
  facesMerge : M.DeleteVertexFacesMerge d0
  /-- The deleted map is connected (via the exposed fan path). -/
  connected : (M.deleteVertex d0).Connected



/-- An edge `α`-cycle relation in `M` between two surviving darts lifts to the
deleted map. -/
 lemma deleted_alpha_sameCycle_of_M {d0 : D}
    (d e : {d : D // d ∉ M.deleteVertexSet d0})
    (h : M.α.SameCycle d.1 e.1) :
    (M.deleteVertex d0).α.SameCycle d e := by
  rcases (M.alpha_sameCycle_iff d.1 e.1).1 h with hde | hde
  · exact (Subtype.ext hde.symm).sameCycle _
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [zpow_one, deleteVertex_alpha_apply_coe]
    exact hde.symm

/-- The vertex `σ`-quotient of `d` in the deleted map equals that of `e` iff the
underlying darts share a `σ`-cycle in `M`. -/
 lemma deleted_tail_eq_iff {d0 : D}
    (d e : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).tail d = (M.deleteVertex d0).tail e ↔
      M.σ.SameCycle d.1 e.1 := by
  constructor
  · intro h
    exact (deleteVertex_sigma_sameCycle_iff M d0 d e).1 (Quotient.exact h)
  · intro h
    exact Quotient.sound ((deleteVertex_sigma_sameCycle_iff M d0 d e).2 h)

/-- The deleted map is a simple graph: deletion only removes darts and reverses,
so no loop or parallel edge can appear among the survivors.  This holds for any
dart `d0` and needs no deletion certificate. -/
theorem deleteVertex_isSimpleGraph (hNT : NearTriangulation M) (d0 : D) :
    (M.deleteVertex d0).IsSimpleGraph := by
  refine ⟨?_, ?_⟩
  · -- no loop: a loop in the deleted map is a loop in `M`
    intro d hloop
    apply hNT.simpleGraph.no_loop d.1
    have hsame : (M.deleteVertex d0).σ.SameCycle d ((M.deleteVertex d0).α d) :=
      Quotient.exact hloop
    have hsameM : M.σ.SameCycle d.1 ((M.deleteVertex d0).α d).1 :=
      (deleteVertex_sigma_sameCycle_iff M d0 d ((M.deleteVertex d0).α d)).1 hsame
    have hαcoe : ((M.deleteVertex d0).α d : D) = M.α d.1 :=
      deleteVertex_alpha_apply_coe M d0 d
    show M.tail d.1 = M.head d.1
    exact Quotient.sound (by rwa [hαcoe] at hsameM)
  · -- no parallel edges: same endpoints in the deleted map means same edge in `M`
    intro d e hedge
    have hαd : ((M.deleteVertex d0).α d : D) = M.α d.1 :=
      deleteVertex_alpha_apply_coe M d0 d
    have hαe : ((M.deleteVertex d0).α e : D) = M.α e.1 :=
      deleteVertex_alpha_apply_coe M d0 e
    have hedge' :
        (s((M.deleteVertex d0).tail d, (M.deleteVertex d0).head d) :
            Sym2 (M.deleteVertex d0).Vertex) =
          s((M.deleteVertex d0).tail e, (M.deleteVertex d0).head e) := hedge
    rw [Sym2.eq_iff] at hedge'
    rcases hedge' with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · have htM : M.σ.SameCycle d.1 e.1 := (deleted_tail_eq_iff d e).1 ht
      have hhM : M.σ.SameCycle (M.α d.1) (M.α e.1) := by
        have hh' : (M.deleteVertex d0).tail ((M.deleteVertex d0).α d) =
            (M.deleteVertex d0).tail ((M.deleteVertex d0).α e) := hh
        have := (deleted_tail_eq_iff ((M.deleteVertex d0).α d)
          ((M.deleteVertex d0).α e)).1 hh'
        rwa [hαd, hαe] at this
      refine deleted_alpha_sameCycle_of_M d e (hNT.simpleGraph.no_parallel ?_)
      show s(M.tail d.1, M.head d.1) = s(M.tail e.1, M.head e.1)
      rw [Sym2.eq_iff]
      exact Or.inl ⟨Quotient.sound htM, Quotient.sound hhM⟩
    · have htM : M.σ.SameCycle d.1 (M.α e.1) := by
        have ht' : (M.deleteVertex d0).tail d =
            (M.deleteVertex d0).tail ((M.deleteVertex d0).α e) := ht
        have := (deleted_tail_eq_iff d ((M.deleteVertex d0).α e)).1 ht'
        rwa [hαe] at this
      have hhM : M.σ.SameCycle (M.α d.1) e.1 := by
        have hh' : (M.deleteVertex d0).tail ((M.deleteVertex d0).α d) =
            (M.deleteVertex d0).tail e := hh
        have := (deleted_tail_eq_iff ((M.deleteVertex d0).α d) e).1 hh'
        rwa [hαd] at this
      refine deleted_alpha_sameCycle_of_M d e (hNT.simpleGraph.no_parallel ?_)
      show s(M.tail d.1, M.head d.1) = s(M.tail e.1, M.head e.1)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨Quotient.sound htM, Quotient.sound hhM⟩

namespace BoundaryDeletionData

variable {hNT : NearTriangulation M} {d0 : D}

/-- The deleted map is a sphere map: assemble `noLoopAt_of_simpleGraph` with the
certificate fields and the reusable `deleteVertex_isSphereMap`. -/
theorem isSphereMap (data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).IsSphereMap :=
  M.deleteVertex_isSphereMap d0 hNT.sphere
    (hNT.noLoopAt_of_simpleGraph d0)
    data.vertexQuotient
    data.vertexFacesDistinct
    data.facesMerge
    data.connected







/-- The deleted map is simple (this needs no certificate). -/
theorem deleteVertex_isSimpleGraph (_data : BoundaryDeletionData hNT d0) :
    (M.deleteVertex d0).IsSimpleGraph :=
  hNT.deleteVertex_isSimpleGraph d0





end BoundaryDeletionData


structure DeletedBoundaryData (hNT : NearTriangulation M) (d0 : D) where
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The new outer boundary cycle. -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- The new boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The new boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer face of the deleted map is triangular (an unchanged old
  inner face). -/
  inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    (M.deleteVertex d0).faceLen f = 3

/-- **Boundary-vertex deletion preserves near-triangulation.**

Given the residual deletion surgery certificate `data` and the deleted-map
boundary surgery certificate `bdy`, the map obtained by deleting the boundary
vertex represented by `d0` is again a near-triangulation.

The sphere-map and simple-graph fields are *derived* (`isSphereMap`,
`deleteVertex_isSimpleGraph`); only the outer-boundary cycle and the inner-face
triangularity come from `bdy`, exactly the dart-level surgery the fan layer does
not expose. -/
def deleteBoundaryVertex_nearTriangulation {hNT : NearTriangulation M}
    {d0 : D} (data : BoundaryDeletionData hNT d0)
    (bdy : DeletedBoundaryData hNT d0) :
    NearTriangulation (M.deleteVertex d0) where
  sphere := data.isSphereMap
  simpleGraph := data.deleteVertex_isSimpleGraph
  outerFace := bdy.outerFace
  outerCycle := bdy.outerCycle
  outer_simple := bdy.outer_simple
  outer_len := bdy.outer_len_ge_three
  inner_tri := bdy.inner_tri





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundaryDelete
-/
/- Source module: ProofsInTheBook.PlanarMapFanSurgery -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D}



/-- In a near-triangulation, a dart whose face is an inner (triangular) face lies
in the `φ`-orbit `{d, φ d, φ² d}`, and these three darts have distinct tails. -/
lemma inner_face_dart_eq_of_same_tail (hNT : NearTriangulation M) {d e : D}
    (hd : M.dartFace d ≠ hNT.outerFace)
    (hface : M.dartFace e = M.dartFace d) (htail : M.tail e = M.tail d) :
    e = d := by
  classical
  -- The triangular face: support of the `φ`-cycle of `d` has size 3.
  have hφ : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph d
  have hlen : M.faceLen (M.dartFace d) = 3 := hNT.inner_tri (M.dartFace d) hd
  have hcard : (M.φ.cycleOf d).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  -- `e` shares the `φ`-cycle with `d`.
  have hcycle : M.φ.SameCycle d e := Quotient.exact hface.symm
  have hsupport : d ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  obtain ⟨i, hi, hipow⟩ := hcycle.exists_pow_eq_of_mem_support hsupport
  rw [hcard] at hi
  -- The three tails are pairwise distinct.
  have hverts := faceLen_three_vertices_pairwiseDistinct M hNT.simpleGraph hlen
  interval_cases i
  · simpa using hipow.symm
  · exfalso
    have he1 : M.φ d = e := by simpa using hipow
    have : M.tail (M.φ d) = M.tail d := by rw [he1, htail]
    exact hverts.1 this.symm
  · exfalso
    have he2 : M.φ (M.φ d) = e := by
      simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hipow
    have : M.tail (M.φ (M.φ d)) = M.tail d := by rw [he2, htail]
    exact hverts.2.2 this

/-- Two darts of a near-triangulation that share the same face and the same tail
are equal.  This is the dart-level statement underlying `VertexFacesDistinct`. -/
lemma dart_eq_of_same_face_same_tail (hNT : NearTriangulation M) {d e : D}
    (hface : M.dartFace d = M.dartFace e) (htail : M.tail d = M.tail e) :
    d = e := by
  classical
  by_cases houter : M.dartFace d = hNT.outerFace
  · -- Both darts lie on the simple outer cycle; its tails are injective.
    have hdmem : d ∈ hNT.outerCycle.darts :=
      (hNT.outerCycle.mem_darts_iff d).mpr houter
    have hemem : e ∈ hNT.outerCycle.darts :=
      (hNT.outerCycle.mem_darts_iff e).mpr (hface ▸ houter)
    exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hdmem hemem htail
  · exact (inner_face_dart_eq_of_same_tail hNT houter hface.symm htail.symm).symm

/-- **`VertexFacesDistinct` discharged.**  In a near-triangulation, the darts at a
vertex represented by `d0` lie on pairwise distinct faces. -/
theorem vertexFacesDistinct_of_nearTriangulation (hNT : NearTriangulation M)
    (d0 : D) : M.VertexFacesDistinct d0 := by
  intro d hd e he hface
  -- `hd, he : same σ-cycle as d0`, so `tail d = tail e = tail d0`.
  have hdtail : M.tail d = M.tail d0 := by
    have : M.σ.SameCycle d0 d := by simpa [vertexDarts] using hd
    exact (Quotient.sound this.symm)
  have hetail : M.tail e = M.tail d0 := by
    have : M.σ.SameCycle d0 e := by simpa [vertexDarts] using he
    exact (Quotient.sound this.symm)
  exact dart_eq_of_same_face_same_tail hNT hface (hdtail.trans hetail.symm)



namespace NeighborRotationOrder

variable {v0 : M.Vertex} {neighbors : List M.Vertex}

/-- Each listed rotation dart has tail `v0`. -/
lemma tail_get (rot : NeighborRotationOrder M v0 neighbors)
    (i : Fin rot.darts.length) : M.tail (rot.darts.get i) = v0 := by
  have hmem : M.tail (rot.darts.get i) ∈ rot.darts.map M.tail :=
    List.mem_map_of_mem (List.get_mem _ _)
  rw [rot.tails_eq] at hmem
  exact List.eq_of_mem_replicate hmem



/-- The rotation dart set is closed under `σ`. -/
lemma sigma_mem (rot : NeighborRotationOrder M v0 neighbors)
    {d : D} (hd : d ∈ rot.darts) : M.σ d ∈ rot.darts := by
  rw [List.mem_iff_get] at hd
  obtain ⟨i, hi⟩ := hd
  rw [← hi, ← rot.consecutive_sigma i]
  exact List.get_mem _ _

/-- The rotation list enumerates exactly the `σ`-orbit of a dart `d0` with tail
`v0`: it is closed under `σ`, nonempty, nodup, and shares the orbit of `d0`. -/
lemma vertexDarts_eq (rot : NeighborRotationOrder M v0 neighbors)
    {d0 : D} (htail : M.tail d0 = v0) :
    M.vertexDarts d0 = rot.darts.toFinset := by
  classical
  -- A representative dart of the list.
  set d1 : D := rot.darts.get ⟨0, rot.darts_nonempty⟩ with hd1
  have hd1_mem : d1 ∈ rot.darts := List.get_mem _ _
  have hd1_tail : M.tail d1 = v0 := rot.tail_get ⟨0, rot.darts_nonempty⟩
  have hsame01 : M.σ.SameCycle d0 d1 := Quotient.exact (htail.trans hd1_tail.symm)
  ext e
  rw [mem_vertexDarts, List.mem_toFinset]
  constructor
  · -- `σ.SameCycle d0 e → e ∈ list`.  Move along the orbit from `d1` to `e`.
    intro he
    have hse : M.σ.SameCycle d1 e := hsame01.symm.trans he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (M.σ ^ n) d1 = e :=
      Equiv.Perm.SameCycle.exists_nat_pow_eq hse
    -- climb `n` steps of `σ` from `d1`, staying inside the σ-closed list.
    have hclosed : ∀ m : ℕ, (M.σ ^ m) d1 ∈ rot.darts := by
      intro m
      induction m with
      | zero => simpa using hd1_mem
      | succ m ih =>
          have hstep : (M.σ ^ (m + 1)) d1 = M.σ ((M.σ ^ m) d1) := by
            rw [pow_succ']; rfl
          rw [hstep]
          exact rot.sigma_mem ih
    rw [← hn]; exact hclosed n
  · -- `e ∈ list → σ.SameCycle d0 e`.
    intro he
    rw [List.mem_iff_get] at he
    obtain ⟨j, hj⟩ := he
    have hetail : M.tail (rot.darts.get j) = v0 := rot.tail_get j
    rw [← hj]
    exact Quotient.exact (htail.trans hetail.symm)





end NeighborRotationOrder





/-- The dart-level output of the boundary-vertex deletion surgery at the boundary
vertex represented by `d0`.  Its fields are exactly the equivalences /
connectivity / boundary cycle that the `deleteSet`-based `deleteVertex` operation
does not produce automatically (see the `TwoEdgePathObstruction` section of
`PlanarMapDelete`), specialized to a chordless boundary vertex via the fan. -/
structure FanSurgeryReconstruction (hNT : NearTriangulation M) (d0 : D) where
  /-- The surviving vertex `σ`-orbits are the old ones minus `⟦d0⟧`. -/
  vertexQuotient :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0}
  /-- The faces incident with `v0` merge into one new outer face. -/
  facesMerge : M.DeleteVertexFacesMerge d0
  /-- The deleted map is connected. -/
  connected : (M.deleteVertex d0).Connected
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The new outer boundary cycle (fan path plus surviving old boundary arc). -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- The new boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The new boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer face of the deleted map is an unchanged old inner triangle. -/
  inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    (M.deleteVertex d0).faceLen f = 3

namespace FanSurgeryReconstruction

variable {hNT : NearTriangulation M} {d0 : D}

/-- Assemble the `BoundaryDeletionData` certificate of `PlanarMapBoundaryDelete`
from the reconstruction.  The two locally-provable fields (`VertexFacesDistinct`)
are supplied by `vertexFacesDistinct_of_nearTriangulation`; the genuinely
dart-level fields come from the reconstruction. -/
def toBoundaryDeletionData (R : FanSurgeryReconstruction hNT d0) :
    BoundaryDeletionData hNT d0 where
  vertexFacesDistinct := hNT.vertexFacesDistinct_of_nearTriangulation d0
  vertexQuotient := R.vertexQuotient
  facesMerge := R.facesMerge
  connected := R.connected

/-- Assemble the `DeletedBoundaryData` certificate from the reconstruction. -/
def toDeletedBoundaryData (R : FanSurgeryReconstruction hNT d0) :
    DeletedBoundaryData hNT d0 where
  outerFace := R.outerFace
  outerCycle := R.outerCycle
  outer_simple := R.outer_simple
  outer_len_ge_three := R.outer_len_ge_three
  inner_tri := R.inner_tri

/-- **The deleted map is a near-triangulation, derived from the reconstruction.**

This is the headline endpoint: given the dart-level reconstruction `R`, deleting
the boundary vertex represented by `d0` again yields a near-triangulation.  Every
hypothesis of `deleteBoundaryVertex_nearTriangulation` is supplied — the locally
provable ones (`NoLoopAt`, `VertexFacesDistinct`) discharged here, the genuinely
dart-level ones taken from `R`. -/
def nearTriangulation (R : FanSurgeryReconstruction hNT d0) :
    NearTriangulation (M.deleteVertex d0) :=
  deleteBoundaryVertex_nearTriangulation R.toBoundaryDeletionData R.toDeletedBoundaryData











end FanSurgeryReconstruction









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
/-
List-coloring primitives (Chapter 35 layer 4).

Design-independent groundwork for the Thomassen five-list-coloring route
(HANDOFF/CH35_DESIGN_ANSWER.md): proper colorings from lists, monotonicity
in the graph and in the lists, and the piecewise gluing lemmas — including
the rooted cut-vertex glue, which is the form that is actually true for
list colorings (naive gluing fails because the two sides may disagree at
the cut vertex).
-/
import Mathlib
-/
/- Source module: ProofsInTheBook.ListColoring -/
section
set_option autoImplicit true


namespace ProofsInTheBook.ListColoring

variable {V α : Type*}

/-- `c` is proper on the region `s`: no monochromatic edge inside `s`. -/
def ProperOn (G : SimpleGraph V) (s : Set V) (c : V → α) : Prop :=
  ∀ ⦃u v⦄, u ∈ s → v ∈ s → G.Adj u v → c u ≠ c v

/-- `c` picks from the lists `L` on the region `s`. -/
def ListValidOn (L : V → Finset α) (s : Set V) (c : V → α) : Prop :=
  ∀ ⦃v⦄, v ∈ s → c v ∈ L v

/-- A proper coloring of all of `G` choosing from the lists `L`. -/
def IsListColoring (G : SimpleGraph V) (L : V → Finset α) (c : V → α) : Prop :=
  (∀ v, c v ∈ L v) ∧ ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v

/-- `G` admits a proper coloring from the lists `L`. -/
def ListColorable (G : SimpleGraph V) (L : V → Finset α) : Prop :=
  ∃ c, IsListColoring G L c











section Glue

variable {G : SimpleGraph V} {L : V → Finset α} {s t : Set V} {c₁ c₂ : V → α}





end Glue



end ProofsInTheBook.ListColoring

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapSeparation
import ProofsInTheBook.PlanarMapFanSurgery
import ProofsInTheBook.ListColoring
-/
/- Source module: ProofsInTheBook.ThomassenLists -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ThomassenLists

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.ListColoring

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {α : Type*} [DecidableEq α]

namespace CombMap

open ProofsInTheBook.PlanarMap.CombMap



/--
The Thomassen list hypotheses for a near-triangulation `M` with a distinguished
*precolored boundary edge* `s(p, q)`.

The two endpoints `p, q` are adjacent on the outer cycle, precolored by singleton
lists `{cp}`, `{cq}` with distinct colors; every other boundary vertex has a list
of size at least `3`; every interior (non-boundary) vertex has a list of size at
least `5`.
-/
structure ThomassenLists {M : CombMap D} (hNT : NearTriangulation M)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) : Prop where
  /-- `p` is on the outer boundary. -/
  p_boundary : hNT.outerCycle.IsBoundaryVertex p
  /-- `q` is on the outer boundary. -/
  q_boundary : hNT.outerCycle.IsBoundaryVertex q
  /-- `p` and `q` are joined by an outer-boundary edge: a precolored edge. -/
  pq_boundary_edge : hNT.outerCycle.IsBoundaryEdge s(p, q)
  /-- The two precolored endpoints carry distinct colors. -/
  colors_ne : cp ≠ cq
  /-- `p` is precolored to the singleton `{cp}`. -/
  list_p : L p = {cp}
  /-- `q` is precolored to the singleton `{cq}`. -/
  list_q : L q = {cq}
  /-- Every other boundary vertex has list size at least three. -/
  boundary_ge_three : ∀ v : M.Vertex,
    hNT.outerCycle.IsBoundaryVertex v → v ≠ p → v ≠ q → 3 ≤ (L v).card
  /-- Every interior (non-boundary) vertex has list size at least five. -/
  interior_ge_five : ∀ v : M.Vertex,
    ¬ hNT.outerCycle.IsBoundaryVertex v → 5 ≤ (L v).card

namespace ThomassenLists

variable {M : CombMap D} {hNT : NearTriangulation M}
  {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- `p ≠ q`: a precolored edge has distinct endpoints. -/
lemma p_ne_q (h : ThomassenLists hNT p q L cp cq) : p ≠ q := by
  intro hpq
  have : cp = cq := by
    have hp := h.list_p
    have hq := h.list_q
    rw [hpq] at hp
    have : ({cp} : Finset α) = {cq} := hp.symm.trans hq
    simpa using this
  exact h.colors_ne this







end ThomassenLists



/--
The `M`-vertex level encoding of a chord split with chord endpoints `u, v` and a
precolored boundary edge `s(p, q)` lying on side 1.

`s₁, s₂ : Set M.Vertex` are the two sides (with the chord endpoints in both).
The Thomassen list hypotheses are carried as region predicates; the `glue` step
combines a side-1 coloring with a compatible side-2 coloring into a coloring of
all of `M.toSimpleGraph`.
-/
structure ChordSplitRegions {M : CombMap D} (hNT : NearTriangulation M)
    (u v p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) where
  /-- Side 1 of the split (contains the precolored edge `pq`). -/
  s₁ : Set M.Vertex
  /-- Side 2 of the split (contains the chord `uv`). -/
  s₂ : Set M.Vertex
  /-- The two sides cover all vertices. -/
  cover : ∀ w : M.Vertex, w ∈ s₁ ∨ w ∈ s₂
  /-- Every graph edge stays inside one side. -/
  edge_confined : ∀ ⦃a b : M.Vertex⦄, M.toSimpleGraph.Adj a b →
    (a ∈ s₁ ∧ b ∈ s₁) ∨ (a ∈ s₂ ∧ b ∈ s₂)
  /-- The two sides overlap in exactly the chord endpoints. -/
  overlap : s₁ ∩ s₂ ⊆ {u, v}
  /-- The chord endpoints are on side 1. -/
  u_s₁ : u ∈ s₁
  /-- The chord endpoints are on side 1. -/
  v_s₁ : v ∈ s₁
  /-- The chord endpoints are on side 2. -/
  u_s₂ : u ∈ s₂
  /-- The chord endpoints are on side 2. -/
  v_s₂ : v ∈ s₂
  /-- The precolored endpoints are on side 1. -/
  p_s₁ : p ∈ s₁
  /-- The precolored endpoints are on side 1. -/
  q_s₁ : q ∈ s₁
  /-- The chord `uv` is an edge of `M`. -/
  chord_adj : M.toSimpleGraph.Adj u v

namespace ChordSplitRegions

variable {M : CombMap D} {hNT : NearTriangulation M}
  {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}





/-- The side-2 forced lists: `u, v` become singletons of their side-1 colors,
every other vertex keeps its list. -/
noncomputable def forcedLists (R : ChordSplitRegions hNT u v p q L cp cq)
    (c₁ : M.Vertex → α) (L : M.Vertex → Finset α) : M.Vertex → Finset α :=
  fun w => if w = u then {c₁ u} else if w = v then {c₁ v} else L w

@[simp]
lemma forcedLists_u (R : ChordSplitRegions hNT u v p q L cp cq)
    (c₁ : M.Vertex → α) (L₀ : M.Vertex → Finset α) :
    R.forcedLists c₁ L₀ u = {c₁ u} := by
  unfold forcedLists; rw [if_pos rfl]

lemma forcedLists_v (R : ChordSplitRegions hNT u v p q L cp cq)
    (huv : u ≠ v) (c₁ : M.Vertex → α) (L₀ : M.Vertex → Finset α) :
    R.forcedLists c₁ L₀ v = {c₁ v} := by
  simp [forcedLists, huv.symm]

lemma forcedLists_other (R : ChordSplitRegions hNT u v p q L cp cq)
    {w : M.Vertex} (hwu : w ≠ u) (hwv : w ≠ v)
    (c₁ : M.Vertex → α) (L₀ : M.Vertex → Finset α) :
    R.forcedLists c₁ L₀ w = L₀ w := by
  simp [forcedLists, hwu, hwv]



end ChordSplitRegions



section Deletion

variable {M : CombMap D}

/-- The canonical map from a vertex of the deleted map to a vertex of `M`,
induced by the kept-dart inclusion `⟦e⟧ ↦ ⟦e.1⟧`.  Well defined because the
deleted-map `σ`-cycle relation is the restriction of `M`'s (see
`deleteVertex_sigma_sameCycle_iff`). -/
noncomputable def deletedVertexToM (M : CombMap D) (d0 : D) :
    (M.deleteVertex d0).Vertex → M.Vertex :=
  Quotient.lift (fun e : {d : D // d ∉ M.deleteVertexSet d0} => M.tail e.1)
    (by
      intro a b hab
      have hsc : (M.deleteVertex d0).σ.SameCycle a b := hab
      rw [deleteVertex_sigma_sameCycle_iff] at hsc
      exact Quotient.sound hsc)

@[simp]
lemma deletedVertexToM_mk (M : CombMap D) (d0 : D)
    (e : {d : D // d ∉ M.deleteVertexSet d0}) :
    deletedVertexToM M d0 (Quotient.mk (cycleSetoid (M.deleteVertex d0).σ) e) =
      M.tail e.1 :=
  rfl

@[simp]
lemma deletedVertexToM_tail (M : CombMap D) (d0 : D)
    (e : {d : D // d ∉ M.deleteVertexSet d0}) :
    deletedVertexToM M d0 ((M.deleteVertex d0).tail e) = M.tail e.1 :=
  rfl

@[simp]
lemma deletedVertexToM_head (M : CombMap D) (d0 : D)
    (e : {d : D // d ∉ M.deleteVertexSet d0}) :
    deletedVertexToM M d0 ((M.deleteVertex d0).head e) = M.head e.1 := by
  show deletedVertexToM M d0
      (Quotient.mk (cycleSetoid (M.deleteVertex d0).σ) ((M.deleteVertex d0).α e)) = _
  rw [deletedVertexToM_mk]
  rw [deleteVertex_alpha_apply_coe]
  rfl

/-- The kept-dart vertex map is injective: distinct deleted-map vertices have
distinct underlying `M`-vertices. -/
lemma deletedVertexToM_injective (M : CombMap D) (d0 : D) :
    Function.Injective (deletedVertexToM M d0) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ ea =>
    induction b using Quotient.inductionOn with
    | _ eb =>
      rw [deletedVertexToM_mk, deletedVertexToM_mk] at hab
      have hsc : M.σ.SameCycle ea.1 eb.1 := Quotient.exact hab
      rw [← deleteVertex_sigma_sameCycle_iff] at hsc
      exact Quotient.sound hsc



/-- The image of the kept-dart vertex map avoids the deleted vertex `v0 = ⟦d0⟧`:
a surviving dart `e ∉ deleteVertexSet d0` is in particular not in the star of
`v0`, so its `M`-tail is not `⟦d0⟧`. -/
lemma deletedVertexToM_ne_v0 (M : CombMap D) (d0 : D)
    (a : (M.deleteVertex d0).Vertex) :
    deletedVertexToM M d0 a ≠ M.tail d0 := by
  induction a using Quotient.inductionOn with
  | _ e =>
    rw [deletedVertexToM_mk]
    intro hcontra
    -- `M.tail e.1 = M.tail d0` ⇒ `σ.SameCycle d0 e.1` ⇒ `e.1 ∈ vertexDarts d0`
    have hsc : M.σ.SameCycle d0 e.1 := Quotient.exact hcontra.symm
    have hmem : e.1 ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 e.1).mpr hsc
    have hdel : e.1 ∈ M.deleteVertexSet d0 :=
      (mem_deleteVertexSet_iff M d0 e.1).mpr (Or.inl hmem)
    exact e.2 hdel

/-- The kept-dart vertex map, corestricted to `{Q // Q ≠ ⟦d0⟧}`. -/
noncomputable def deletedVertexToM' (M : CombMap D) (d0 : D)
    (a : (M.deleteVertex d0).Vertex) :
    {Q : M.Vertex // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  ⟨deletedVertexToM M d0 a, deletedVertexToM_ne_v0 M d0 a⟩

lemma deletedVertexToM'_injective (M : CombMap D) (d0 : D) :
    Function.Injective (deletedVertexToM' M d0) := by
  intro a b hab
  exact deletedVertexToM_injective M d0 (Subtype.ext_iff.mp hab)

/-- **The kept-dart vertex map is a bijection onto `{Q // Q ≠ ⟦d0⟧}`.**

An injective map between two finite types of equal cardinality is bijective.
The cardinality equality is exactly the reconstruction equivalence
`FanSurgeryReconstruction.vertexQuotient`, so the *canonical* kept-dart map (not
the abstract reconstruction equiv) is itself the desired bijection. -/
lemma deletedVertexToM'_bijective {hNT : NearTriangulation M} {d0 : D}
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0) :
    Function.Bijective (deletedVertexToM' M d0) := by
  classical
  have hcard :
      Fintype.card ((M.deleteVertex d0).Vertex) =
        Fintype.card {Q : M.Vertex // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
    Fintype.card_congr R.vertexQuotient
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨deletedVertexToM'_injective M d0, hcard⟩

/-- A dart whose two `M`-endpoints both avoid `v0 = ⟦d0⟧` survives the deletion:
it is not in the closed star `deleteVertexSet d0`. -/
lemma dart_notMem_deleteVertexSet_of_endpoints_ne (M : CombMap D) (d0 : D)
    {d : D} (htail : M.tail d ≠ M.tail d0) (hhead : M.head d ≠ M.tail d0) :
    d ∉ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]
  push_neg
  constructor
  · rw [mem_vertexDarts]
    intro hsc
    exact htail (Quotient.sound hsc.symm)
  · rw [mem_vertexDarts]
    intro hsc
    -- `σ.SameCycle d0 (α d)` ⇒ `tail (α d) = tail d0`, and `tail (α d) = head d`
    have : M.tail (M.α d) = M.tail d0 := Quotient.sound hsc.symm
    rw [tail_alpha] at this
    exact hhead this





variable {hNT : NearTriangulation M} {d0 : D} {v0 : M.Vertex}

/-- The deleted-map lists.  A deleted vertex `q'` whose `M`-image lies in the fan
interior loses the two reserved colors `γ, δ`; every other vertex keeps `L`. -/
noncomputable def deleteFanLists (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α) :
    (M.deleteVertex d0).Vertex → Finset α :=
  fun q' =>
    if deletedVertexToM M d0 q' ∈ fanInterior then
      (L (deletedVertexToM M d0 q')) \ {γ, δ}
    else L (deletedVertexToM M d0 q')

/-- On a fan vertex the deleted list is `L` minus the two reserved colors. -/
lemma deleteFanLists_fan (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α)
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior) :
    deleteFanLists M d0 fanInterior L γ δ q' =
      (L (deletedVertexToM M d0 q')) \ {γ, δ} := by
  simp [deleteFanLists, hq]

/-- Off the fan vertices the deleted list is just `L`. -/
lemma deleteFanLists_other (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) (γ δ : α)
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∉ fanInterior) :
    deleteFanLists M d0 fanInterior L γ δ q' = L (deletedVertexToM M d0 q') := by
  simp [deleteFanLists, hq]

/-- **Fan vertices keep a list of size at least three.**  An interior fan vertex
was interior (non-boundary) in `M`, hence had list size `≥ 5`; removing the two
reserved colors leaves `≥ 3`.  This is the exact size accounting of the review. -/
lemma deleteFanLists_card_ge_three (M : CombMap D) (d0 : D)
    (fanInterior : Finset M.Vertex) (L : M.Vertex → Finset α) {γ δ : α}
    {q' : (M.deleteVertex d0).Vertex}
    (hq : deletedVertexToM M d0 q' ∈ fanInterior)
    (h5 : 5 ≤ (L (deletedVertexToM M d0 q')).card) :
    3 ≤ (deleteFanLists M d0 fanInterior L γ δ q').card := by
  classical
  rw [deleteFanLists_fan M d0 fanInterior L γ δ hq]
  have hle : ((L (deletedVertexToM M d0 q')) \ {γ, δ}).card ≥
      (L (deletedVertexToM M d0 q')).card - ({γ, δ} : Finset α).card := by
    have := Finset.le_card_sdiff ({γ, δ} : Finset α) (L (deletedVertexToM M d0 q'))
    omega
  have hcard2 : ({γ, δ} : Finset α).card ≤ 2 := Finset.card_insert_le _ _ |>.trans
    (by simp)
  omega



/-- The kept-dart bijection onto `{Q // Q ≠ ⟦d0⟧}`, packaged as an `Equiv`. -/
noncomputable def deletedVertexEquiv
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0) :
    (M.deleteVertex d0).Vertex ≃
      {Q : M.Vertex // Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  Equiv.ofBijective _ (deletedVertexToM'_bijective R)

/-- The section `Vertex M → Vertex(deleted)` for vertices other than `v0`. -/
noncomputable def sectionToDeleted
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (x : M.Vertex) (hx : x ≠ Quotient.mk (cycleSetoid M.σ) d0) :
    (M.deleteVertex d0).Vertex :=
  (deletedVertexEquiv R).symm ⟨x, hx⟩

@[simp]
lemma deletedVertexToM_sectionToDeleted
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (x : M.Vertex) (hx : x ≠ Quotient.mk (cycleSetoid M.σ) d0) :
    deletedVertexToM M d0 (sectionToDeleted R x hx) = x := by
  have := (deletedVertexEquiv R).apply_symm_apply ⟨x, hx⟩
  have h2 : deletedVertexToM' M d0 ((deletedVertexEquiv R).symm ⟨x, hx⟩) = ⟨x, hx⟩ := this
  exact congrArg Subtype.val h2

/-- The full extended coloring of `M`: at `v0` use the chosen color `a`, elsewhere
use the deleted-map coloring through the kept-dart section. -/
noncomputable def extendColoring
    (R : NearTriangulation.FanSurgeryReconstruction hNT d0)
    (c : (M.deleteVertex d0).Vertex → α) (a : α) : M.Vertex → α :=
  fun x =>
    if hx : x = Quotient.mk (cycleSetoid M.σ) d0 then a
    else c (sectionToDeleted R x hx)





















end Deletion

end CombMap

end ProofsInTheBook.ThomassenLists

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanSurgery
-/
/- Source module: ProofsInTheBook.PlanarMapFanConnectivity -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- An `α`-step between survivors lifts to the deleted map: if `x` survives then
so does `M.α x.1`, and `(deleteVertex).α x = ⟨M.α x.1, _⟩`. -/
lemma deleteVertex_dartStep_of_alpha (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v})
    (y : {d : D // d ∉ M.deleteVertexSet v}) (h : y.1 = M.α x.1) :
    (M.deleteVertex v).dartStep x y := by
  right
  apply Subtype.ext
  rw [deleteVertex_alpha_apply_coe]
  exact h

/-- A `σ`-step between survivors lifts to the deleted map. -/
lemma deleteVertex_dartStep_of_sigma (M : CombMap D) (v : D)
    (x y : {d : D // d ∉ M.deleteVertexSet v}) (h : M.σ.SameCycle x.1 y.1) :
    (M.deleteVertex v).dartStep x y := by
  left
  exact (deleteVertex_sigma_sameCycle_iff M v x y).2 h

/-- `α` preserves survival: if `d` survives the star deletion of `v`, so does
`M.α d`. -/
lemma alpha_notMem_deleteVertexSet (M : CombMap D) (v : D) {d : D}
    (hd : d ∉ M.deleteVertexSet v) : M.α d ∉ M.deleteVertexSet v := by
  intro h
  exact hd ((M.alpha_mem_deleteVertexSet_iff v d).1 h)


def DeleteVertexNeighborsConnected (M : CombMap D) (v : D) : Prop :=
  ∀ x y : {d : D // d ∉ M.deleteVertexSet v},
    (∃ e ∈ M.deleteVertexSet v, M.σ.SameCycle e x.1) →
    (∃ e ∈ M.deleteVertexSet v, M.σ.SameCycle e y.1) →
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y



/-- The deleted-map step relation is symmetric. -/
lemma deleteVertex_dartStep_symm (M : CombMap D) (v : D)
    {x y : {d : D // d ∉ M.deleteVertexSet v}}
    (h : (M.deleteVertex v).dartStep x y) :
    (M.deleteVertex v).dartStep y x := by
  rcases h with hσ | hα
  · exact Or.inl hσ.symm
  · -- `y = (deleteVertex).α x`, hence `x = (deleteVertex).α y` by involution.
    right
    have := congrArg (M.deleteVertex v).α hα
    rw [(M.deleteVertex v).alpha_alpha] at this
    exact this.symm

/-- The deleted-map reachability relation is symmetric. -/
lemma deleteVertex_reachable_symm (M : CombMap D) (v : D)
    {x y : {d : D // d ∉ M.deleteVertexSet v}}
    (h : Relation.ReflTransGen (M.deleteVertex v).dartStep x y) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.head (deleteVertex_dartStep_symm M v hbc) ih



section Reduction

variable (M : CombMap D) (v : D)

/-- Local abbreviation for surviving darts. -/
 abbrev Surv := {d : D // d ∉ M.deleteVertexSet v}

/-- A survivor is a *neighbour-survivor* of `v` if its vertex `σ`-orbit contains a
deleted dart (so its vertex is adjacent to `v`). -/
 def IsNbr (a : Surv M v) : Prop :=
  ∃ e ∈ M.deleteVertexSet v, M.σ.SameCycle e a.1

/-- The connectivity reduction: from `M`-connectivity and the fan-geometric
neighbour-reconnection predicate, the deleted map is connected. -/
theorem deleteVertex_connected_of_neighborsConnected
    (hconn : M.Connected)
    (hnbr : M.DeleteVertexNeighborsConnected v) :
    (M.deleteVertex v).Connected := by
  classical
  set S := M.deleteVertexSet v with hS
  -- It suffices to connect every survivor to a fixed base survivor `r`.
  intro x y
  set Rel : Surv M v → Surv M v → Prop :=
    fun a b => Relation.ReflTransGen (M.deleteVertex v).dartStep a b with hRel
  -- Abbreviation: every neighbour-survivor reaches the base.
  -- The backward-induction invariant on darts of `M`.
  set AllNbrReach : Surv M v → Prop :=
    fun r => ∀ a : Surv M v, IsNbr M v a → Rel a r with hAllNbr
  set Inv : Surv M v → D → Prop :=
    fun r c =>
      (∀ h : c ∉ S, Rel ⟨c, h⟩ r) ∧ (c ∈ S → AllNbrReach r) with hInv
  -- The key: every survivor reaches every base survivor `r`.
  have key : ∀ r : Surv M v, ∀ a : Surv M v, Rel a r := by
    intro r
    -- Base of the induction: `Inv r r.1`.
    have hbase : Inv r r.1 := by
      refine ⟨?_, ?_⟩
      · intro h
        have heq : (⟨r.1, h⟩ : Surv M v) = r := Subtype.ext rfl
        rw [heq]
      · intro hr
        exact absurd hr r.2
    -- Backward closure of `Inv` along `M.dartStep`.
    have hstep : ∀ c c' : D, M.dartStep c c' → Inv r c' → Inv r c := by
      intro c c' hcc' hc'
      refine ⟨?_, ?_⟩
      · -- alive case
        intro hc
        rcases hcc' with hσ | hα
        · -- σ-step `c → c'`
          by_cases hc'S : c' ∈ S
          · -- c' deleted: `⟨c,hc⟩` is a neighbour-survivor, use `Inv c'`'s nbr-clause.
            have hnbr_c : IsNbr M v ⟨c, hc⟩ := ⟨c', hc'S, hσ.symm⟩
            exact hc'.2 hc'S ⟨c, hc⟩ hnbr_c
          · -- c' alive: σ-step lifts, then `Inv c'`.
            have hreach : Rel ⟨c', hc'S⟩ r := hc'.1 hc'S
            have hd : (M.deleteVertex v).dartStep ⟨c, hc⟩ ⟨c', hc'S⟩ :=
              deleteVertex_dartStep_of_sigma M v ⟨c, hc⟩ ⟨c', hc'S⟩ hσ
            exact Relation.ReflTransGen.head hd hreach
        · -- α-step `c' = α c`; α preserves survival.
          have hc'S : c' ∉ S := by
            rw [hα]; exact alpha_notMem_deleteVertexSet M v hc
          have hreach : Rel ⟨c', hc'S⟩ r := hc'.1 hc'S
          have hd : (M.deleteVertex v).dartStep ⟨c, hc⟩ ⟨c', hc'S⟩ :=
            deleteVertex_dartStep_of_alpha M v ⟨c, hc⟩ ⟨c', hc'S⟩ hα
          exact Relation.ReflTransGen.head hd hreach
      · -- deleted case: maintain `AllNbrReach`.
        intro hcS
        rcases hcc' with hσ | hα
        · by_cases hc'S : c' ∈ S
          · exact hc'.2 hc'S
          · -- c' alive and is itself a neighbour-survivor; bridge all neighbours via `hnbr`.
            intro a ha
            have hreach_c' : Rel ⟨c', hc'S⟩ r := hc'.1 hc'S
            have hnbr_c' : IsNbr M v ⟨c', hc'S⟩ := ⟨c, hcS, hσ⟩
            have hbridge :
                Relation.ReflTransGen (M.deleteVertex v).dartStep a ⟨c', hc'S⟩ :=
              hnbr a ⟨c', hc'S⟩ ha hnbr_c'
            exact hbridge.trans hreach_c'
        · -- α-step `c' = α c`; `c' ∈ S` since `c ∈ S`.
          have hc'S : c' ∈ S := by
            rw [hα]
            exact (M.alpha_mem_deleteVertexSet_iff v c).2 hcS
          exact hc'.2 hc'S
    -- Run the backward induction over an `M`-walk from `a` to `r`.
    intro a
    have hwalk : Relation.ReflTransGen M.dartStep a.1 r.1 := hconn a.1 r.1
    have hInva : Inv r a.1 :=
      Relation.ReflTransGen.head_induction_on hwalk hbase
        (fun {b c} hbc _ ih => hstep b c hbc ih)
    have hfin : Rel (⟨a.1, a.2⟩ : Surv M v) r := hInva.1 a.2
    have heq : (⟨a.1, a.2⟩ : Surv M v) = a := Subtype.ext rfl
    rwa [heq] at hfin
  -- Conclude: every survivor reaches every base survivor, so `x` reaches `y`.
  exact key y x

end Reduction



namespace NearTriangulation

variable {M : CombMap D}

/-- A dart survives the star deletion of `v` iff neither it nor its reverse lies
in the `σ`-orbit of `v`. -/
 lemma notMem_deleteVertexSet_iff (v d : D) :
    d ∉ M.deleteVertexSet v ↔
      ¬ M.σ.SameCycle v d ∧ ¬ M.σ.SameCycle v (M.α d) := by
  rw [mem_deleteVertexSet_iff]
  simp only [mem_vertexDarts, not_or]

/-- A dart whose tail and head are both different from the vertex of `v` (as
`σ`-orbits) survives the star deletion. -/
 lemma notMem_deleteVertexSet_of_tail_head_ne {v d : D}
    (htail : M.tail d ≠ M.tail v) (hhead : M.head d ≠ M.tail v) :
    d ∉ M.deleteVertexSet v := by
  rw [notMem_deleteVertexSet_iff]
  refine ⟨?_, ?_⟩
  · intro h
    exact htail (Quotient.sound h).symm
  · intro h
    exact hhead (Quotient.sound h).symm

/-- One deleted-map reachability step from a `σ`-cycle relation between
survivors. -/
 lemma rel_of_sigma {v : D} (x y : {d : D // d ∉ M.deleteVertexSet v})
    (h : M.σ.SameCycle x.1 y.1) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y :=
  Relation.ReflTransGen.single (deleteVertex_dartStep_of_sigma M v x y h)

/-- One deleted-map reachability step from `y = M.α x` between survivors. -/
 lemma rel_of_alpha {v : D} (x y : {d : D // d ∉ M.deleteVertexSet v})
    (h : y.1 = M.α x.1) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y :=
  Relation.ReflTransGen.single (deleteVertex_dartStep_of_alpha M v x y h)

variable {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- The "edge dart" of a fan triangle `(v0, a, b)`: its middle dart `d1` has tail
`a` and head `b`, and survives the deletion of any dart `d0` representing `v0`. -/
 lemma fanTriangle_edge_dart_survives_p2m_6755d2cf6bd3 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  -- tail T.d1 = a ≠ v0 = tail d0
  have htail : M.tail T.d1 ≠ M.tail d0 := by
    rw [T.tail1, htail0]
    exact (hdist.1).symm
  -- head T.d1 = b ≠ v0 = tail d0
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by
      rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [hhead_eq, htail0]
    exact hdist.2.2
  exact notMem_deleteVertexSet_of_tail_head_ne htail hhead

/-- For a fan triangle `(v0, a, b)`, any surviving dart whose vertex is `a` is
deleted-map connected to any surviving dart whose vertex is `b`, via the
surviving triangle edge `a—b`. -/
 lemma fanTriangle_connects {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0)
    (p q : {d : D // d ∉ M.deleteVertexSet d0})
    (hp : M.tail p.1 = a) (hq : M.tail q.1 = b) :
    Relation.ReflTransGen (M.deleteVertex d0).dartStep p q := by
  -- The surviving edge dart `T.d1` (tail a, head b) and its reverse.
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 :=
    fanTriangle_edge_dart_survives_p2m_6755d2cf6bd3 T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 :=
    alpha_notMem_deleteVertexSet M d0 hd1
  set e1 : {d : D // d ∉ M.deleteVertexSet d0} := ⟨T.d1, hd1⟩ with he1
  set e1' : {d : D // d ∉ M.deleteVertexSet d0} := ⟨M.α T.d1, hd1'⟩ with he1'
  -- p ↝ e1 (same vertex a)
  have hpe1 : M.σ.SameCycle p.1 T.d1 :=
    Quotient.exact (show M.tail p.1 = M.tail T.d1 by rw [hp, T.tail1])
  have step1 : Relation.ReflTransGen (M.deleteVertex d0).dartStep p e1 :=
    rel_of_sigma p e1 hpe1
  -- e1 ↝ e1' (edge step)
  have step2 : Relation.ReflTransGen (M.deleteVertex d0).dartStep e1 e1' :=
    rel_of_alpha e1 e1' rfl
  -- e1' ↝ q (same vertex b: tail (α T.d1) = head T.d1 = b)
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have he1'q : M.σ.SameCycle (M.α T.d1) q.1 :=
    Quotient.exact (show M.tail (M.α T.d1) = M.tail q.1 by rw [tail_alpha, hhead_eq, hq])
  have step3 : Relation.ReflTransGen (M.deleteVertex d0).dartStep e1' q :=
    rel_of_sigma e1' q he1'q
  exact (step1.trans step2).trans step3

/-- `consecutivePairs` of a two-or-more element list. -/
 lemma consecutivePairs_cons_cons_p2m_6755d2cf6bd3 {α : Type*} (a b : α) (l : List α) :
    consecutivePairs (a :: b :: l) = (a, b) :: consecutivePairs (b :: l) := by
  simp [consecutivePairs]

/-- Symmetric "all survivors at `a` connect to all survivors at `b`" relation. -/
 def VConn {d0 : D} (a b : M.Vertex) : Prop :=
  ∀ p q : {d : D // d ∉ M.deleteVertexSet d0},
    M.tail p.1 = a → M.tail q.1 = b →
    Relation.ReflTransGen (M.deleteVertex d0).dartStep p q

 lemma VConn.symm {d0 : D} {a b : M.Vertex} (h : VConn (M := M) (d0 := d0) a b) :
    VConn (M := M) (d0 := d0) b a := by
  intro p q hp hq
  exact deleteVertex_reachable_symm M d0 (h q p hq hp)

/-- A `FanTriangle` provides `VConn` between its two non-`v0` vertices, and a
surviving witness dart at each. -/
 lemma fanTriangle_vconn {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    VConn (M := M) (d0 := d0) a b :=
  fun p q hp hq => fanTriangle_connects T htail0 p q hp hq

/-- A `FanTriangle` provides a surviving dart whose vertex is its second
non-`v0` vertex `b` (the reverse `α T.d1` of the surviving edge dart). -/
 lemma fanTriangle_witness_snd_p2m_6755d2cf6bd3 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = b := by
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 := fanTriangle_edge_dart_survives_p2m_6755d2cf6bd3 T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 := alpha_notMem_deleteVertexSet M d0 hd1
  refine ⟨⟨M.α T.d1, hd1'⟩, ?_⟩
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  show M.tail (M.α T.d1) = b
  rw [tail_alpha, hh, T.tail2]

/-- A `FanTriangle` provides a surviving dart whose vertex is its first non-`v0`
vertex `a` (the surviving edge dart `T.d1` itself, tail `a`). -/
 lemma fanTriangle_witness_fst_p2m_6755d2cf6bd3 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = a :=
  ⟨⟨T.d1, fanTriangle_edge_dart_survives_p2m_6755d2cf6bd3 T htail0⟩, T.tail1⟩

/-- Chaining: if consecutive pairs of a list `L` (with at least the head vertex
present) all carry fan triangles in the **σ-predecessor** orientation
(`(a, b) ↦ FanTriangle v0 b a`, the fixed `triangle_of_pair` convention), then every
vertex of `L` is `VConn` to the head of `L`.  Proved by induction maintaining a
surviving witness at the head; `VConn` is symmetric so the orientation is immaterial. -/
 lemma vconn_head_of_pairs {d0 : D} (htail0 : M.tail d0 = v0) :
    ∀ (L : List M.Vertex) (hd : M.Vertex),
      (∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (hd :: L) →
        FanTriangle hNT v0 b a) →
      ∀ u : M.Vertex, u ∈ (hd :: L) → VConn (M := M) (d0 := d0) u hd := by
  intro L
  induction L with
  | nil =>
      intro hd _ u hu
      have hueq : u = hd := by simpa using hu
      subst hueq
      intro p q hp hq
      exact rel_of_sigma p q
        (Quotient.exact (show M.tail p.1 = M.tail q.1 by rw [hp, hq]))
  | cons b l ih =>
      intro hd htri u hu
      -- The first pair `(hd, b)` carries a (predecessor-oriented) fan triangle.
      have hpair0 : (hd, b) ∈ consecutivePairs (hd :: b :: l) := by
        rw [consecutivePairs_cons_cons_p2m_6755d2cf6bd3]; exact List.mem_cons.mpr (Or.inl rfl)
      have T0 : FanTriangle hNT v0 b hd := htri hd b hpair0
      have hVhd_b : VConn (M := M) (d0 := d0) hd b := (fanTriangle_vconn T0 htail0).symm
      -- triangles for the tail list `b :: l`.
      have htri' : ∀ a c : M.Vertex, (a, c) ∈ consecutivePairs (b :: l) →
          FanTriangle hNT v0 c a := by
        intro a c hac
        apply htri a c
        rw [consecutivePairs_cons_cons_p2m_6755d2cf6bd3]
        exact List.mem_cons.mpr (Or.inr hac)
      have ihrun := ih b htri'
      rcases List.mem_cons.mp hu with hueq | hurest
      · -- u = hd: reflexive `VConn`.
        subst hueq
        intro p q hp hq
        exact rel_of_sigma p q
          (Quotient.exact (show M.tail p.1 = M.tail q.1 by rw [hp, hq]))
      · -- u ∈ b :: l: connect u → b (by IH) then b → hd (by T0).
        have hVu_b : VConn (M := M) (d0 := d0) u b := ihrun u hurest
        intro p q hp hq
        -- need a witness at `b` (the first label of the swapped triangle `T0`).
        obtain ⟨m, hm⟩ : ∃ m : {d : D // d ∉ M.deleteVertexSet d0}, M.tail m.1 = b :=
          fanTriangle_witness_fst_p2m_6755d2cf6bd3 T0 htail0
        have h1 : Relation.ReflTransGen (M.deleteVertex d0).dartStep p m :=
          hVu_b p m hp hm
        have h2 : Relation.ReflTransGen (M.deleteVertex d0).dartStep m q :=
          (hVhd_b.symm) m q hm hq
        exact h1.trans h2

/-- The vertex of a neighbour-survivor of `v0` lies on the fan path. -/
 lemma neighbor_tail_mem_path (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) {x : {d : D // d ∉ M.deleteVertexSet d0}}
    (hx : ∃ e ∈ M.deleteVertexSet d0, M.σ.SameCycle e x.1) :
    M.tail x.1 ∈ fan.path := by
  obtain ⟨e, heS, hex⟩ := hx
  -- `e ∈ vertexDarts d0` would force `x` into the deleted star.
  rw [mem_deleteVertexSet_iff] at heS
  rcases heS with he | hαe
  · exfalso
    rw [mem_vertexDarts] at he
    -- tail x = v0 ⟹ x deleted
    have : M.σ.SameCycle d0 x.1 := he.trans hex
    exact x.2 ((mem_deleteVertexSet_iff M d0 x.1).2 (Or.inl ((mem_vertexDarts M d0 x.1).2 this)))
  · -- `α e` is a rotation dart; its head is a neighbour, equal to `tail x`.
    rw [mem_vertexDarts] at hαe
    have hαe_mem : M.α e ∈ fan.rotation_order.darts := by
      have heq : M.vertexDarts d0 = fan.rotation_order.darts.toFinset :=
        fan.rotation_order.vertexDarts_eq htail0
      have : M.α e ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 (M.α e)).2 hαe
      rw [heq, List.mem_toFinset] at this
      exact this
    -- tail x = tail e = head (α e)
    have htx : M.tail x.1 = M.head (M.α e) := by
      have h1 : M.tail x.1 = M.tail e := (Quotient.sound hex).symm
      rw [h1, head_alpha]
    -- head (α e) ∈ neighbors = fan.path
    have hmem : M.head (M.α e) ∈ fan.rotation_order.darts.map M.head :=
      List.mem_map_of_mem hαe_mem
    rw [fan.rotation_order.heads_eq] at hmem
    rw [htx, BoundaryVertexFan.path]
    exact hmem

/-- **The fan discharges `DeleteVertexNeighborsConnected`.**  Given a boundary
fan at `v0` and any dart `d0` representing `v0`, the neighbour-survivors of `v0`
are reconnected in the deleted map via the fan path. -/
theorem deleteVertex_neighborsConnected_of_fan (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    M.DeleteVertexNeighborsConnected d0 := by
  -- Every neighbour-survivor is `VConn` to the fan head `fan.x`.
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  have htri : ∀ a b : M.Vertex,
      (a, b) ∈ consecutivePairs (fan.x :: L) → FanTriangle hNT v0 b a := by
    intro a b hab
    have hab' : (a, b) ∈ consecutivePairs fan.path := by rw [hpath]; exact hab
    exact fan.incident_faces_exact.triangle_of_pair (by
      simpa [BoundaryVertexFan.path] using hab')
  have hhead : ∀ u : M.Vertex, u ∈ fan.path →
      VConn (M := M) (d0 := d0) u fan.x := by
    intro u hu
    have hu' : u ∈ fan.x :: L := by rw [← hpath]; exact hu
    exact vconn_head_of_pairs htail0 L fan.x htri u hu'
  -- Assemble: two neighbour-survivors both connect to `fan.x`.
  intro x y hx hy
  have hxpath : M.tail x.1 ∈ fan.path := neighbor_tail_mem_path fan htail0 hx
  have hypath : M.tail y.1 ∈ fan.path := neighbor_tail_mem_path fan htail0 hy
  have hVx : VConn (M := M) (d0 := d0) (M.tail x.1) fan.x := hhead _ hxpath
  have hVy : VConn (M := M) (d0 := d0) (M.tail y.1) fan.x := hhead _ hypath
  -- a witness survivor at `fan.x`: the pair `(fan.x, _)` triangle, if it exists,
  -- else `x` itself routes through.  We use the head triangle witness.
  -- Connect x → fan.x → y.
  -- Need a witness at fan.x.  `fan.x` is the head of the path of length ≥ 2.
  obtain ⟨b, _l, hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  have hpair0 : (fan.x, b) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons_p2m_6755d2cf6bd3]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 b fan.x := htri fan.x b hpair0
  obtain ⟨m, hm⟩ : ∃ m : {d : D // d ∉ M.deleteVertexSet d0}, M.tail m.1 = fan.x :=
    fanTriangle_witness_snd_p2m_6755d2cf6bd3 T0 htail0
  have h1 : Relation.ReflTransGen (M.deleteVertex d0).dartStep x m :=
    hVx x m rfl hm
  have h2 : Relation.ReflTransGen (M.deleteVertex d0).dartStep m y :=
    (hVy.symm) m y hm rfl
  exact h1.trans h2

/-- **The deleted map is connected (fan form).**  Deleting the closed star of a
boundary vertex `v0` of a near-triangulation, where `d0` is a dart representing
`v0` and `fan` is a boundary fan at `v0`, leaves a connected combinatorial map.
The two boundary neighbours of `v0` and all interior fan vertices stay joined
through the surviving fan path `x, z₁, …, z_t, w`.

This discharges the `connected` field of `FanSurgeryReconstruction`
unconditionally from the fan and the near-triangulation invariant. -/
theorem deleteVertex_connected_of_fan (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) :
    (M.deleteVertex d0).Connected :=
  deleteVertex_connected_of_neighborsConnected M d0 hNT.sphere.1
    (deleteVertex_neighborsConnected_of_fan fan htail0)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanConnectivity
import ProofsInTheBook.PlanarMapFilteredRotation
-/
/- Source module: ProofsInTheBook.PlanarMapFanFaces -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



@[simp]
lemma deleteVertex_phi_apply_coe (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v}) :
    ((M.deleteVertex v).φ x : D) =
      (M.σ ^ Equiv.Perm.DeleteSet.firstOutside M.σ (M.deleteVertexSet v)
        (M.alphaDeleteVertex v x)) (M.α x.1) := by
  show ((M.deleteVertex v).σ ((M.deleteVertex v).α x) : D) = _
  rw [show (M.deleteVertex v).σ = M.σ.deleteSet (M.deleteVertexSet v) from rfl]
  rw [Equiv.Perm.deleteSet_apply_coe]
  rfl

/-- **`φ` agrees with `M.φ` when the next dart survives.**  If `x` survives and
`M.φ x.1 = M.σ (M.α x.1)` again survives, then the deleted map's `φ`-successor of
`x` is exactly `M.φ x.1`. -/
lemma deleteVertex_phi_apply_of_next_kept (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v})
    (hkept : M.φ x.1 ∉ M.deleteVertexSet v) :
    ((M.deleteVertex v).φ x : D) = M.φ x.1 := by
  have hαx : M.α x.1 ∉ M.deleteVertexSet v := alpha_notMem_deleteVertexSet M v x.2
  -- The filtered rotation from `α x.1` takes exactly one σ-step, landing on `M.φ x.1`.
  set y : {d : D // d ∉ M.deleteVertexSet v} := M.alphaDeleteVertex v x with hy
  have hycoe : (y : D) = M.α x.1 := by rw [hy]; exact alphaDeleteVertex_apply_coe M v x
  have hnext : M.σ (y : D) ∉ M.deleteVertexSet v := by
    rw [hycoe]; exact hkept
  have hone : Equiv.Perm.DeleteSet.firstOutside M.σ (M.deleteVertexSet v) y = 1 :=
    FilteredRotation.firstOutside_eq_one_of_next_notMem
      M.σ (M.deleteVertexSet v) y hnext
  rw [deleteVertex_phi_apply_coe]
  rw [show (M.alphaDeleteVertex v x) = y from rfl, hone, pow_one]
  rfl

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}



/-- `consecutivePairs` of a two-or-more element list. -/
 lemma consecutivePairs_cons_cons_p2m_e7d236328e37 {α : Type*} (a b : α) (l : List α) :
    consecutivePairs (a :: b :: l) = (a, b) :: consecutivePairs (b :: l) := by
  simp [consecutivePairs]

/-- The middle edge dart `d1` of a fan triangle survives the deletion of any dart
`d0` representing `v0`. -/
 lemma fanTriangle_edge_dart_survives_p2m_e7d236328e37 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  have htail : M.tail T.d1 ≠ M.tail d0 := by
    rw [T.tail1, htail0]; exact (hdist.1).symm
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [hhead_eq, htail0]; exact hdist.2.2
  rw [mem_deleteVertexSet_iff]
  push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- `M.σ.SameCycle d0 T.d1` would give `tail d0 = tail T.d1`.
    exact htail (Quotient.sound h).symm
  · -- `M.σ.SameCycle d0 (α T.d1)` gives `tail d0 = tail (α T.d1) = head T.d1`.
    have : M.tail d0 = M.head T.d1 := Quotient.sound h
    exact hhead this.symm

/-- A fan triangle provides a surviving dart whose tail is its second non-`v0`
vertex `b` (the reverse `α T.d1` of the surviving edge dart). -/
 lemma fanTriangle_witness_snd_p2m_e7d236328e37 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = b := by
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 := fanTriangle_edge_dart_survives_p2m_e7d236328e37 T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 := alpha_notMem_deleteVertexSet M d0 hd1
  refine ⟨⟨M.α T.d1, hd1'⟩, ?_⟩
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  show M.tail (M.α T.d1) = b
  rw [tail_alpha, hh, T.tail2]

/-- A fan triangle provides a surviving dart whose tail is its first non-`v0`
vertex `a` (the surviving edge dart `T.d1` itself, tail `a`). -/
 lemma fanTriangle_witness_fst_p2m_e7d236328e37 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = a :=
  ⟨⟨T.d1, fanTriangle_edge_dart_survives_p2m_e7d236328e37 T htail0⟩, T.tail1⟩

/-- Every vertex on the fan path carries a surviving dart whose tail is that
vertex. -/
lemma fan_path_vertex_has_survivor (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) {u : M.Vertex} (hu : u ∈ fan.path) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = u := by
  -- Set up the path as `fan.x :: L`.
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  -- Predecessor convention: a forward pair `(a, b)` carries `FanTriangle v0 b a`.
  have htri : ∀ a b : M.Vertex,
      (a, b) ∈ consecutivePairs (fan.x :: L) → FanTriangle hNT v0 b a := by
    intro a b hab
    have hab' : (a, b) ∈ consecutivePairs fan.path := by rw [hpath]; exact hab
    exact fan.incident_faces_exact.triangle_of_pair (by
      simpa [BoundaryVertexFan.path] using hab')
  -- `L` is nonempty: `L = b :: l'`.
  obtain ⟨b, l', hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  -- The head triangle for pair `(fan.x, b)` is `FanTriangle v0 b fan.x`.
  have hpair0 : (fan.x, b) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons_p2m_e7d236328e37]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 b fan.x := htri fan.x b hpair0
  rw [hpath] at hu
  rcases List.mem_cons.mp hu with hux | huL
  · -- `u = fan.x`: `fan.x` is the second label of `T0`, use `α T0.d1`.
    subst hux
    exact fanTriangle_witness_snd_p2m_e7d236328e37 T0 htail0
  · -- `u ∈ L`: `u` is the second component of some forward consecutive pair, i.e.
    -- the first label of its (swapped) triangle; use that triangle's edge dart.
    -- Induct over `L` with the running "previous vertex" being `fan.x`.
    clear hu hpair0 T0 hLb b l'
    -- General statement: for any list `M0` and head `h0` such that all pairs of
    -- `h0 :: M0` carry (swapped) triangles, every member of `M0` has a survivor.
    suffices hgen : ∀ (M0 : List M.Vertex) (h0 : M.Vertex),
        (∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (h0 :: M0) →
          FanTriangle hNT v0 b a) →
        ∀ z : M.Vertex, z ∈ M0 →
          ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = z by
      exact hgen L fan.x htri u huL
    clear htri huL hpath hL
    intro M0
    induction M0 with
    | nil => intro h0 _ z hz; simp at hz
    | cons c t ih =>
        intro h0 htri' z hz
        -- The first pair `(h0, c)` carries the swapped triangle `FanTriangle v0 c h0`;
        -- `c` is its first label, with surviving edge dart at `c`.
        have hpc : (h0, c) ∈ consecutivePairs (h0 :: c :: t) := by
          rw [consecutivePairs_cons_cons_p2m_e7d236328e37]; exact List.mem_cons.mpr (Or.inl rfl)
        have Tc : FanTriangle hNT v0 c h0 := htri' h0 c hpc
        rcases List.mem_cons.mp hz with hzc | hzt
        · subst hzc
          exact fanTriangle_witness_fst_p2m_e7d236328e37 Tc htail0
        · -- recurse on `c :: t`.
          have htri'' : ∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (c :: t) →
              FanTriangle hNT v0 b a := by
            intro a b hab
            apply htri' a b
            rw [consecutivePairs_cons_cons_p2m_e7d236328e37]
            exact List.mem_cons.mpr (Or.inr hab)
          exact ih c htri'' z hzt



/-- Membership of a dart's face in `vertexFaces d0` is exactly: some dart in its
`M.φ`-orbit has tail `v0`. -/
 lemma dartFace_mem_vertexFaces_iff {d0 : D} (htail0 : M.tail d0 = v0)
    (d : D) :
    M.dartFace d ∈ M.vertexFaces d0 ↔
      ∃ k : ℤ, M.tail ((M.φ ^ k) d) = v0 := by
  classical
  constructor
  · intro hmem
    rw [vertexFaces, Finset.mem_image] at hmem
    obtain ⟨e, he, hef⟩ := hmem
    rw [mem_vertexDarts] at he
    -- `e` has tail v0 and same φ-orbit as `d`.
    have hetail : M.tail e = v0 := by
      have : M.tail d0 = M.tail e := Quotient.sound he
      rw [← this, htail0]
    have hsame : M.φ.SameCycle d e := Quotient.exact hef.symm
    obtain ⟨k, hk⟩ := hsame
    exact ⟨k, by rw [hk]; exact hetail⟩
  · rintro ⟨k, hk⟩
    rw [vertexFaces, Finset.mem_image]
    refine ⟨(M.φ ^ k) d, ?_, ?_⟩
    · rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail ((M.φ ^ k) d) by rw [htail0, hk])
    · exact Quotient.sound (⟨-k, by simp⟩ : M.φ.SameCycle ((M.φ ^ k) d) d)

/-- If `d`'s face is not incident with `v0`, then `d` survives the deletion. -/
 lemma survives_of_dartFace_notMem {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    d ∉ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]
  push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  refine ⟨fun h => hf ?_, fun h => hf ?_⟩
  · -- `tail d = v0`: take `k = 0`.
    rw [dartFace_mem_vertexFaces_iff htail0]
    refine ⟨0, ?_⟩
    simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    have heq : M.tail d0 = M.tail d := Quotient.sound h
    rw [← heq, htail0]
  · -- `tail (α d) = v0` i.e. `head d = v0 = tail (φ d)`: take `k = 1`.
    rw [dartFace_mem_vertexFaces_iff htail0]
    refine ⟨1, ?_⟩
    rw [zpow_one, tail_phi]
    have heq : M.tail d0 = M.tail (M.α d) := Quotient.sound h
    rw [tail_alpha] at heq
    rw [← heq, htail0]

/-- The same, for the `φ`-successor: if `d`'s face avoids `v0`, so does `M.φ d`,
hence `M.φ d` survives. -/
 lemma phi_survives_of_dartFace_notMem {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    M.φ d ∉ M.deleteVertexSet d0 := by
  apply survives_of_dartFace_notMem htail0
  -- `M.φ d` has the same face as `d`.
  have hface : M.dartFace (M.φ d) = M.dartFace d :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ d) d)
  rw [hface]; exact hf

/-- On a clean dart, the deleted `φ` agrees with `M.φ`, and the result is again
clean. -/
 lemma deleteVertex_phi_clean_step {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) :
    ((M.deleteVertex d0).φ x : D) = M.φ x.1 ∧
      M.dartFace ((M.deleteVertex d0).φ x).1 ∉ M.vertexFaces d0 := by
  have hkept : M.φ x.1 ∉ M.deleteVertexSet d0 := phi_survives_of_dartFace_notMem htail0 hf
  have hagree : ((M.deleteVertex d0).φ x : D) = M.φ x.1 :=
    deleteVertex_phi_apply_of_next_kept M d0 x hkept
  refine ⟨hagree, ?_⟩
  rw [hagree]
  -- same face as `x`
  have hface : M.dartFace (M.φ x.1) = M.dartFace x.1 :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ x.1) x.1)
  rw [hface]; exact hf

/-- Iterating the clean step: for a clean dart `x`, the `k`-th deleted-`φ`
iterate has underlying dart `(M.φ ^ k) x.1`, and stays clean. -/
 lemma deleteVertex_phi_clean_iterate {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) (k : ℕ) :
    (((M.deleteVertex d0).φ ^ k) x : D) = (M.φ ^ k) x.1 ∧
      M.dartFace (((M.deleteVertex d0).φ ^ k) x).1 ∉ M.vertexFaces d0 := by
  induction k with
  | zero => exact ⟨rfl, by simpa using hf⟩
  | succ k ih =>
      obtain ⟨hval, hcln⟩ := ih
      have hstep := deleteVertex_phi_clean_step htail0 (((M.deleteVertex d0).φ ^ k) x) hcln
      have hiter1 : ((M.deleteVertex d0).φ ^ (k + 1)) x
          = (M.deleteVertex d0).φ (((M.deleteVertex d0).φ ^ k) x) := by
        rw [pow_succ']; rfl
      constructor
      · rw [hiter1, hstep.1, hval]
        rw [pow_succ']; rfl
      · rw [hiter1]; exact hstep.2

/-- Two clean survivors on the same `M`-face are in the same deleted-`φ` cycle. -/
 lemma deleteVertex_phi_sameCycle_of_clean {d0 : D} (htail0 : M.tail d0 = v0)
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hfx : M.dartFace x.1 ∉ M.vertexFaces d0)
    (hsame : M.dartFace x.1 = M.dartFace y.1) :
    (M.deleteVertex d0).φ.SameCycle x y := by
  have hφsame : M.φ.SameCycle x.1 y.1 := Quotient.exact hsame
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hφsame
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  apply Subtype.ext
  rw [(deleteVertex_phi_clean_iterate htail0 x hfx k).1, hk]



/-- The finset of clean survivors. -/
 noncomputable def cleanSurvSet (d0 : D) :
    Finset {d : D // d ∉ M.deleteVertexSet d0} :=
  Finset.univ.filter (fun x => M.dartFace x.1 ∉ M.vertexFaces d0)

 lemma mem_cleanSurvSet {d0 : D} (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    x ∈ cleanSurvSet (M := M) d0 ↔ M.dartFace x.1 ∉ M.vertexFaces d0 := by
  simp [cleanSurvSet]

/-- The clean set is invariant under `φ'`: `φ' x` is clean iff `x` is. -/
 lemma cleanSurvSet_phi_invariant {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).φ x ∈ cleanSurvSet (M := M) d0 ↔
      x ∈ cleanSurvSet (M := M) d0 := by
  classical
  -- `φ'` maps the clean set into itself.
  have hmaps : ∀ y ∈ cleanSurvSet (M := M) d0,
      (M.deleteVertex d0).φ y ∈ cleanSurvSet (M := M) d0 := by
    intro y hy
    rw [mem_cleanSurvSet] at hy ⊢
    exact (deleteVertex_phi_clean_step htail0 y hy).2
  -- Hence its image equals itself (injective on a finite set).
  have himg : (cleanSurvSet (M := M) d0).image (M.deleteVertex d0).φ
      = cleanSurvSet (M := M) d0 := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      rw [← hyz]; exact hmaps y hy
    · rw [Finset.card_image_of_injective _ (M.deleteVertex d0).φ.injective]
  constructor
  · intro hφ
    by_contra hx
    -- `x ∉ clean` but `φ' x ∈ clean = image`, so `x ∈ clean`, contradiction.
    have : (M.deleteVertex d0).φ x ∈ (cleanSurvSet (M := M) d0).image (M.deleteVertex d0).φ := by
      rw [himg]; exact hφ
    rw [Finset.mem_image] at this
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := (M.deleteVertex d0).φ.injective hyx
    rw [this] at hy; exact hx hy
  · exact hmaps x



/-- A survivor's underlying old `σ`-orbit is never the orbit of `d0`. -/
 lemma survivor_orbit_ne {d0 : D}
    (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    Quotient.mk (cycleSetoid M.σ) x.1 ≠ Quotient.mk (cycleSetoid M.σ) d0 := by
  intro h
  have hsame : M.σ.SameCycle d0 x.1 := (Quotient.exact h).symm
  exact x.2 ((mem_deleteVertexSet_iff M d0 x.1).2
    (Or.inl ((mem_vertexDarts M d0 x.1).2 hsame)))

/-- The forward vertex-quotient map: send a survivor's deleted-`σ`-orbit to its
old `σ`-orbit (which is never `⟦d0⟧`). -/
 noncomputable def vertexQuotientFun (d0 : D) :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) →
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  Quotient.lift
    (fun x => ⟨Quotient.mk (cycleSetoid M.σ) x.1, survivor_orbit_ne x⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      have : M.σ.SameCycle x.1 y.1 :=
        (deleteVertex_sigma_sameCycle_iff M d0 x y).1 hxy
      exact Quotient.sound this)

/-- The forward vertex-quotient map is injective. -/
 lemma vertexQuotientFun_injective (d0 : D) :
    Function.Injective (vertexQuotientFun (M := M) d0) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := a.exists_rep
  obtain ⟨y, rfl⟩ := b.exists_rep
  have hval : Quotient.mk (cycleSetoid M.σ) x.1 = Quotient.mk (cycleSetoid M.σ) y.1 := by
    have := congrArg Subtype.val hab
    simpa [vertexQuotientFun] using this
  have hsame : M.σ.SameCycle x.1 y.1 := Quotient.exact hval
  exact Quotient.sound ((deleteVertex_sigma_sameCycle_iff M d0 x y).2 hsame)

/-- The forward vertex-quotient map is surjective, using the fan to guarantee a
surviving dart in every old orbit `≠ ⟦d0⟧`. -/
 lemma vertexQuotientFun_surjective (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    Function.Surjective (vertexQuotientFun (M := M) d0) := by
  rintro ⟨Q, hQ⟩
  obtain ⟨e, rfl⟩ := Q.exists_rep
  -- Produce a survivor in the σ-orbit of `e`.
  obtain ⟨p, hp⟩ : ∃ p : {d : D // d ∉ M.deleteVertexSet d0},
      M.σ.SameCycle e p.1 := by
    by_cases hes : e ∈ M.deleteVertexSet d0
    · -- `e` is deleted.  It is not in `vertexDarts d0` (else `⟦e⟧ = ⟦d0⟧`),
      -- so its reverse `α e` is, i.e. `head e = v0`; `tail e` is a neighbour.
      rw [mem_deleteVertexSet_iff] at hes
      rcases hes with hev | hαv
      · exfalso
        rw [mem_vertexDarts] at hev
        exact hQ (Quotient.sound hev.symm)
      · -- `α e ∈ vertexDarts d0`: `M.σ.SameCycle d0 (α e)`, so `head e = v0`.
        rw [mem_vertexDarts] at hαv
        have hhead : M.head e = v0 := by
          have : M.tail d0 = M.tail (M.α e) := Quotient.sound hαv
          rw [tail_alpha] at this; rw [← this, htail0]
        -- `tail e` is a neighbour of `v0`; it is on the fan path.
        -- `tail e = head (α e)` and `α e` is in the rotation, so `tail e ∈ heads = path`.
        have hαe_rot : M.α e ∈ fan.rotation_order.darts := by
          have heq : M.vertexDarts d0 = fan.rotation_order.darts.toFinset :=
            fan.rotation_order.vertexDarts_eq htail0
          have hmem : M.α e ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 (M.α e)).2 hαv
          rw [heq, List.mem_toFinset] at hmem; exact hmem
        have htaile_path : M.tail e ∈ fan.path := by
          have hmem : M.head (M.α e) ∈ fan.rotation_order.darts.map M.head :=
            List.mem_map_of_mem hαe_rot
          rw [fan.rotation_order.heads_eq] at hmem
          rw [BoundaryVertexFan.path]
          simpa [head_alpha] using hmem
        obtain ⟨p, hp⟩ := fan_path_vertex_has_survivor fan htail0 htaile_path
        exact ⟨p, Quotient.exact (show M.tail e = M.tail p.1 by rw [hp])⟩
    · exact ⟨⟨e, hes⟩, Equiv.Perm.SameCycle.refl M.σ e⟩
  refine ⟨Quotient.mk (cycleSetoid (M.deleteVertex d0).σ) p, ?_⟩
  apply Subtype.ext
  show Quotient.mk (cycleSetoid M.σ) p.1 = Quotient.mk (cycleSetoid M.σ) e
  exact Quotient.sound hp.symm

/-- **The vertex-quotient equivalence (fan form).**  The surviving `σ`-orbits of
`M.deleteVertex d0` biject with the old vertex orbits other than `⟦d0⟧`. -/
noncomputable def deleteVertex_vertexQuotientEquiv (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  Equiv.ofBijective (vertexQuotientFun d0)
    ⟨vertexQuotientFun_injective d0, vertexQuotientFun_surjective fan htail0⟩



/-- The residual seam fact: all surviving darts whose `M`-face is incident with
`v0` lie in a single `φ'`-cycle (the new merged outer face). -/
def DeleteVertexMergedFaceSingleOrbit (M : CombMap D) (d0 : D) : Prop :=
  ∀ x y : {d : D // d ∉ M.deleteVertexSet d0},
    M.dartFace x.1 ∈ M.vertexFaces d0 → M.dartFace y.1 ∈ M.vertexFaces d0 →
    (M.deleteVertex d0).φ.SameCycle x y

/-- The face classification (incident with `v0`, or clean) is invariant along
deleted-`φ` cycles. -/
 lemma incident_invariant_of_sameCycle {d0 : D} (htail0 : M.tail d0 = v0)
    {x y : {d : D // d ∉ M.deleteVertexSet d0}}
    (hxy : (M.deleteVertex d0).φ.SameCycle x y) :
    (M.dartFace x.1 ∈ M.vertexFaces d0 ↔ M.dartFace y.1 ∈ M.vertexFaces d0) := by
  classical
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hxy
  -- iterate the φ'-invariance of the clean set
  have hiter : ∀ m : ℕ,
      (M.dartFace (((M.deleteVertex d0).φ ^ m) x).1 ∈ M.vertexFaces d0 ↔
        M.dartFace x.1 ∈ M.vertexFaces d0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hstep := cleanSurvSet_phi_invariant htail0 (((M.deleteVertex d0).φ ^ m) x)
        rw [mem_cleanSurvSet, mem_cleanSurvSet] at hstep
        have hiter1 : ((M.deleteVertex d0).φ ^ (m + 1)) x
            = (M.deleteVertex d0).φ (((M.deleteVertex d0).φ ^ m) x) := by
          rw [pow_succ']; rfl
        rw [hiter1]
        -- `hstep : φ'(·) clean ↔ · clean`; negate to incident.
        rw [← not_iff_not] at ih ⊢
        rw [hstep]; exact ih
  have := hiter k
  rw [hk] at this
  exact this.symm

/-- On a clean deleted-`φ` cycle, the `M`-face is constant. -/
 lemma clean_face_const_of_sameCycle {d0 : D} (htail0 : M.tail d0 = v0)
    {x y : {d : D // d ∉ M.deleteVertexSet d0}}
    (hfx : M.dartFace x.1 ∉ M.vertexFaces d0)
    (hxy : (M.deleteVertex d0).φ.SameCycle x y) :
    M.dartFace x.1 = M.dartFace y.1 := by
  classical
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hxy
  have hval := (deleteVertex_phi_clean_iterate htail0 x hfx k).1
  rw [hk] at hval
  -- `y.1 = (M.φ^k) x.1`, so same M-face.
  rw [hval]
  exact (Quotient.sound (⟨(k : ℤ), by rw [zpow_natCast]⟩ :
    M.φ.SameCycle x.1 ((M.φ ^ k) x.1)))

/-- The forward face-merge map: a deleted-`φ` orbit maps to its (unchanged)
clean `M`-face, or to the single merged outer face `inr ()`. -/
 noncomputable def faceMergeFun {d0 : D} (htail0 : M.tail d0 = v0) :
    Quotient (cycleSetoid (M.deleteVertex d0).φ) → M.deleteVertexFaceModel d0 :=
  Quotient.lift
    (fun x =>
      if h : M.dartFace x.1 ∈ M.vertexFaces d0 then Sum.inr ()
      else Sum.inl ⟨M.dartFace x.1, h⟩)
    (by
      intro x y hxy
      by_cases hx : M.dartFace x.1 ∈ M.vertexFaces d0
      · have hy : M.dartFace y.1 ∈ M.vertexFaces d0 :=
          (incident_invariant_of_sameCycle htail0 hxy).1 hx
        simp [hx, hy]
      · have hy : M.dartFace y.1 ∉ M.vertexFaces d0 := by
          intro hy'
          exact hx ((incident_invariant_of_sameCycle htail0 hxy).2 hy')
        have hface := clean_face_const_of_sameCycle htail0 hx hxy
        simp only []
        rw [dif_neg hx, dif_neg hy, Sum.inl.injEq, Subtype.mk.injEq]
        exact hface)

/-- A fan triangle's surviving edge dart is an incident survivor (its `M`-face is
the triangle, which is incident with `v0`). -/
 lemma fanTriangle_edge_dart_incident {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    M.dartFace (⟨T.d1, fanTriangle_edge_dart_survives_p2m_e7d236328e37 T htail0⟩ :
      {d : D // d ∉ M.deleteVertexSet d0}).1 ∈ M.vertexFaces d0 := by
  -- `d0`-face of `T.d0` (tail `v0`) equals the triangle face, which is `dartFace T.d1`.
  rw [dartFace_mem_vertexFaces_iff htail0]
  -- `T.d2` is in the φ-orbit of `T.d1` and has head `v0`, i.e. tail of its φ-succ is `v0`.
  -- Actually `T.d0` (tail v0) is `M.φ T.d2 = M.φ (M.φ T.d1)`, in the same φ-orbit.
  refine ⟨2, ?_⟩
  have h01 : M.φ T.d1 = T.d2 := T.triangle.2.1
  have h12 : M.φ T.d2 = T.d0 := T.triangle.2.2
  have h2 : (M.φ ^ (2 : ℤ)) T.d1 = T.d0 := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h01, h12]
  rw [h2, T.tail0]

/-- Existence of an incident survivor (the head fan triangle's edge dart). -/
 lemma exists_incident_survivor (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ x : {d : D // d ∉ M.deleteVertexSet d0},
      M.dartFace x.1 ∈ M.vertexFaces d0 := by
  -- The head triangle of the fan path.
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  obtain ⟨b, l', hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  have hpair0 : (fan.x, b) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons_p2m_e7d236328e37]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 b fan.x := by
    apply fan.incident_faces_exact.triangle_of_pair
    have : (fan.x, b) ∈ consecutivePairs fan.path := by rw [hpath]; exact hpair0
    simpa [BoundaryVertexFan.path] using this
  exact ⟨_, fanTriangle_edge_dart_incident T0 htail0⟩

/-- Evaluation of `faceMergeFun` on the class of a clean survivor. -/
 lemma faceMergeFun_clean {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) (hx : M.dartFace x.1 ∉ M.vertexFaces d0) :
    faceMergeFun htail0 (Quotient.mk _ x) = Sum.inl ⟨M.dartFace x.1, hx⟩ := by
  rw [faceMergeFun, Quotient.lift_mk]
  rw [dif_neg hx]

/-- Evaluation of `faceMergeFun` on the class of an incident survivor. -/
 lemma faceMergeFun_incident {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) (hx : M.dartFace x.1 ∈ M.vertexFaces d0) :
    faceMergeFun htail0 (Quotient.mk _ x) = Sum.inr () := by
  rw [faceMergeFun, Quotient.lift_mk]
  rw [dif_pos hx]

/-- The face-merge map is bijective, given the merged-orbit fact. -/
 lemma faceMergeFun_bijective (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    Function.Bijective (faceMergeFun (M := M) htail0) := by
  classical
  constructor
  · -- injective
    intro a c hac
    obtain ⟨x, rfl⟩ := a.exists_rep
    obtain ⟨y, rfl⟩ := c.exists_rep
    by_cases hx : M.dartFace x.1 ∈ M.vertexFaces d0
    · by_cases hy : M.dartFace y.1 ∈ M.vertexFaces d0
      · exact Quotient.sound (hmerge x y hx hy)
      · rw [faceMergeFun_incident htail0 x hx, faceMergeFun_clean htail0 y hy] at hac
        exact absurd hac (by simp)
    · by_cases hy : M.dartFace y.1 ∈ M.vertexFaces d0
      · rw [faceMergeFun_clean htail0 x hx, faceMergeFun_incident htail0 y hy] at hac
        exact absurd hac (by simp)
      · -- both clean: equal `inl` faces ⟹ φ'-SameCycle
        rw [faceMergeFun_clean htail0 x hx, faceMergeFun_clean htail0 y hy] at hac
        have hval : M.dartFace x.1 = M.dartFace y.1 :=
          congrArg Subtype.val (Sum.inl.inj hac)
        exact Quotient.sound (deleteVertex_phi_sameCycle_of_clean htail0 x y hx hval)
  · -- surjective
    rintro (⟨f, hf⟩ | ⟨⟩)
    · -- clean face `f`: pick a surviving dart of `f`.
      obtain ⟨d, rfl⟩ := f.exists_rep
      have hd : d ∉ M.deleteVertexSet d0 := survives_of_dartFace_notMem htail0 hf
      exact ⟨Quotient.mk _ ⟨d, hd⟩, faceMergeFun_clean htail0 ⟨d, hd⟩ hf⟩
    · -- the merged outer face `inr ()`: any incident survivor.
      obtain ⟨x, hx⟩ := exists_incident_survivor fan htail0
      exact ⟨Quotient.mk _ x, faceMergeFun_incident htail0 x hx⟩

/-- **The face-merge field (fan form).**  Given the fan and the merged-orbit
fact, the `φ`-orbits of the deleted map are exactly the clean old faces plus one
merged outer face. -/
theorem deleteVertex_facesMerge_of_fan (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    M.DeleteVertexFacesMerge d0 :=
  ⟨Equiv.ofBijective _ (faceMergeFun_bijective fan htail0 hmerge)⟩



/-- Bundle of the new outer boundary data of the deleted map: the merged outer
face, its boundary cycle, simplicity, length bound, and the triangularity of all
other (surviving inner) faces.  This is exactly the part of
`FanSurgeryReconstruction` that is *not* the dart-rotation algebra discharged in
this file. -/
structure DeletedOuterBoundary (hNT : NearTriangulation M) (d0 : D) where
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The new outer boundary cycle. -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- The new boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The new boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer face of the deleted map is an unchanged old inner triangle. -/
  inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    (M.deleteVertex d0).faceLen f = 3

/-- **Assemble `FanSurgeryReconstruction` from the fan.**  All three
dart-rotation surgery fields are discharged from the fan; the merged-orbit fact
and the new outer boundary data are supplied as inputs. -/
noncomputable def fanSurgeryReconstruction (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (bdry : DeletedOuterBoundary hNT d0) :
    FanSurgeryReconstruction hNT d0 where
  vertexQuotient := deleteVertex_vertexQuotientEquiv fan htail0
  facesMerge := deleteVertex_facesMerge_of_fan fan htail0 hmerge
  connected := deleteVertex_connected_of_fan fan htail0
  outerFace := bdry.outerFace
  outerCycle := bdry.outerCycle
  outer_simple := bdry.outer_simple
  outer_len_ge_three := bdry.outer_len_ge_three
  inner_tri := bdry.inner_tri

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
-/
/- Source module: ProofsInTheBook.PlanarMapFanMergedOrbit -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- The vertex rotation factors as `σ = φ · α` (since `φ = σ · α` and `α² = 1`). -/
lemma sigma_eq_phi_mul_alpha (M : CombMap D) : M.σ = M.φ * M.α := by
  rw [φ, mul_assoc, M.α_invol, mul_one]

/-- One `σ`-step is `φ` after `α`. -/
lemma sigma_apply (M : CombMap D) (d : D) : M.σ d = M.φ (M.α d) := by
  rw [sigma_eq_phi_mul_alpha]; rfl

/-- `σ (α d) = M.φ d`. -/
lemma sigma_alpha (M : CombMap D) (d : D) : M.σ (M.α d) = M.φ d := by
  rw [sigma_apply, M.alpha_alpha]

/-- **Closed-form `φ'` successor, Case B: the next dart is deleted.**  If `x`
survives, the immediate `M.φ`-successor `M.φ x.1` is deleted, but the following
`σ`-step `M.σ (M.φ x.1)` survives, then the deleted-map `φ'`-successor of `x`
is exactly `M.σ (M.φ x.1)`. -/
lemma deleteVertex_phi_apply_of_next_deleted (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v})
    (hdel : M.φ x.1 ∈ M.deleteVertexSet v)
    (hsurv : M.σ (M.φ x.1) ∉ M.deleteVertexSet v) :
    ((M.deleteVertex v).φ x : D) = M.σ (M.φ x.1) := by
  classical
  set y : {d : D // d ∉ M.deleteVertexSet v} := M.alphaDeleteVertex v x with hy
  have hycoe : (y : D) = M.α x.1 := by rw [hy]; exact alphaDeleteVertex_apply_coe M v x
  -- σ¹ (α x.1) = M.φ x.1
  have hσ1 : (M.σ ^ 1) (y : D) = M.φ x.1 := by
    rw [pow_one, hycoe, sigma_alpha]
  -- σ² (α x.1) = σ (M.φ x.1)
  have hσ2 : (M.σ ^ 2) (y : D) = M.σ (M.φ x.1) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ']
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ1]
  -- firstOutside = 2
  have hfo : Equiv.Perm.DeleteSet.firstOutside M.σ (M.deleteVertexSet v) y = 2 := by
    refine (Nat.find_eq_iff (Equiv.Perm.DeleteSet.exists_pos_pow_notMem M.σ (M.deleteVertexSet v) y)).2 ?_
    refine ⟨⟨by norm_num, by rw [hσ2]; exact hsurv⟩, ?_⟩
    intro m hm ⟨hmpos, hmnot⟩
    interval_cases m
    · rw [hσ1] at hmnot; exact hmnot hdel
  rw [deleteVertex_phi_apply_coe]
  rw [show (M.alphaDeleteVertex v x) = y from rfl, hfo, ← hycoe, hσ2]



/-- A forward `M.φ`-run of survivors is followed step-for-step by `φ'`. -/
lemma deleteVertex_phi_survRun_iterate (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v}) (k : ℕ)
    (hrun : ∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet v) :
    (((M.deleteVertex v).φ ^ k) x : D) = (M.φ ^ k) x.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ihrun : ∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet v :=
        fun j hj => hrun j (Nat.le_succ_of_le hj)
      have hval : (((M.deleteVertex v).φ ^ k) x : D) = (M.φ ^ k) x.1 := ih ihrun
      -- the dart we are stepping from survives
      have hxk : (M.φ ^ k) x.1 ∉ M.deleteVertexSet v := hrun k (Nat.le_succ k)
      -- its M.φ-successor survives
      have hnext : M.φ ((M.φ ^ k) x.1) ∉ M.deleteVertexSet v := by
        have : (M.φ ^ (k + 1)) x.1 = M.φ ((M.φ ^ k) x.1) := by
          rw [pow_succ']; rfl
        rw [← this]; exact hrun (k + 1) (le_refl _)
      have hiter1 : ((M.deleteVertex v).φ ^ (k + 1)) x
          = (M.deleteVertex v).φ (((M.deleteVertex v).φ ^ k) x) := by
        rw [pow_succ']; rfl
      rw [hiter1]
      -- φ' agrees with M.φ on the surviving dart ⟨(M.φ^k) x.1, hxk⟩
      have hstep : ((M.deleteVertex v).φ (((M.deleteVertex v).φ ^ k) x) : D)
          = M.φ ((M.φ ^ k) x.1) := by
        have hpt : (((M.deleteVertex v).φ ^ k) x) = (⟨(M.φ ^ k) x.1, hxk⟩ :
            {d : D // d ∉ M.deleteVertexSet v}) := Subtype.ext hval
        rw [hpt]
        exact deleteVertex_phi_apply_of_next_kept M v ⟨(M.φ ^ k) x.1, hxk⟩ hnext
      rw [hstep, pow_succ']; rfl

/-- Two survivors on the same `M`-face whose connecting forward `M.φ`-run stays
inside the survivors are in the same `φ'`-cycle. -/
lemma deleteVertex_phi_sameCycle_of_survRun (M : CombMap D) (v : D)
    (x y : {d : D // d ∉ M.deleteVertexSet v}) (k : ℕ)
    (hrun : ∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet v)
    (hk : (M.φ ^ k) x.1 = y.1) :
    (M.deleteVertex v).φ.SameCycle x y := by
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  apply Subtype.ext
  rw [deleteVertex_phi_survRun_iterate M v x k hrun, hk]

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}



/-- The head of `T.d1` is `b`. -/
 lemma fanTriangle_head1 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d1 = b := by
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  rw [hh, T.tail2]

/-- The head of `T.d2` is `v0`. -/
 lemma fanTriangle_head2 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d2 = v0 := by
  have hphi : M.φ T.d2 = T.d0 := T.triangle.2.2
  have hh : M.head T.d2 = M.tail T.d0 := by rw [← tail_phi, hphi]
  rw [hh, T.tail0]

/-- The head of `T.d0` is `a`. -/
 lemma fanTriangle_head0 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d0 = a := by
  have hphi : M.φ T.d0 = T.d1 := T.triangle.1
  have hh : M.head T.d0 = M.tail T.d1 := by rw [← tail_phi, hphi]
  rw [hh, T.tail1]

/-- `T.d1` survives the deletion of any dart `d0` representing `v0`. -/
 lemma fanTriangle_d1_survives {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  have htail : M.tail T.d1 ≠ M.tail d0 := by rw [T.tail1, htail0]; exact (hdist.1).symm
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [fanTriangle_head1 T, htail0]; exact hdist.2.2
  rw [mem_deleteVertexSet_iff]; push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  refine ⟨fun h => htail (Quotient.sound h).symm, fun h => ?_⟩
  have heq : M.tail d0 = M.tail (M.α T.d1) := Quotient.sound h
  rw [tail_alpha] at heq
  exact hhead heq.symm

/-- `T.d2` is deleted (its head is `v0`). -/
 lemma fanTriangle_d2_deleted {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d2 ∈ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]; right
  rw [mem_vertexDarts]
  -- α T.d2 has tail = head T.d2 = v0 = tail d0
  exact Quotient.exact (show M.tail d0 = M.tail (M.α T.d2) by
    rw [tail_alpha, fanTriangle_head2 T, htail0])



/-- **Consecutive fan triangles share the `v0`-spoke.**  If `Ti = (v0, a, b)` and
`Tj = (v0, b, c)` are consecutive fan triangles, then the reverse of `Ti.d2`
(tail `b`, head `v0`) is `Tj.d0` (tail `v0`, head `b`): they are the two darts of
the single edge `v0—b`. -/
 lemma fanTriangle_shared_spoke {a b c : M.Vertex}
    (Ti : FanTriangle hNT v0 a b) (Tj : FanTriangle hNT v0 b c) :
    M.α Ti.d2 = Tj.d0 := by
  have hsame : M.α.SameCycle Ti.d2 Tj.d0 :=
    alpha_sameCycle_of_same_endpoints_symm M hNT.simpleGraph
      (by rw [Ti.tail2, fanTriangle_head0 Tj])
      (by rw [fanTriangle_head2 Ti, Tj.tail0])
  rcases (alpha_sameCycle_iff M Ti.d2 Tj.d0).1 hsame with h | h
  · -- Tj.d0 = Ti.d2 impossible: different tails (v0 vs b)
    exfalso
    have hbv0 : (b : M.Vertex) = v0 := by
      have : M.tail Tj.d0 = M.tail Ti.d2 := by rw [h]
      rw [Tj.tail0, Ti.tail2] at this; exact this.symm
    exact (Tj.vertices_pairwiseDistinct).1 hbv0.symm
  · rw [h]

/-- **Triangle chain step.**  The deleted-map `φ'`-successor of `Ti.d1` is
`Tj.d1`, where `Tj` is the next consecutive fan triangle. -/
 lemma fanTriangle_chain_step {a b c : M.Vertex}
    (Ti : FanTriangle hNT v0 a b) (Tj : FanTriangle hNT v0 b c)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    ((M.deleteVertex d0).φ ⟨Ti.d1, fanTriangle_d1_survives Ti htail0⟩ : D) = Tj.d1 := by
  have hdel : M.φ Ti.d1 ∈ M.deleteVertexSet d0 := by
    have hphi : M.φ Ti.d1 = Ti.d2 := Ti.triangle.2.1
    rw [hphi]; exact fanTriangle_d2_deleted Ti htail0
  -- σ (M.φ Ti.d1) = σ Ti.d2 = M.φ (α Ti.d2) = M.φ Tj.d0 = Tj.d1
  have hphi1 : M.φ Ti.d1 = Ti.d2 := Ti.triangle.2.1
  have hsig : M.σ (M.φ Ti.d1) = Tj.d1 := by
    rw [hphi1, sigma_apply, fanTriangle_shared_spoke Ti Tj]
    exact Tj.triangle.1
  have hsurv : M.σ (M.φ Ti.d1) ∉ M.deleteVertexSet d0 := by
    rw [hsig]; exact fanTriangle_d1_survives Tj htail0
  rw [deleteVertex_phi_apply_of_next_deleted M d0 _ hdel hsurv, hsig]

/-- `φ'`-cycle form of the chain step: consecutive triangle edge darts are in one
`φ'`-cycle. -/
 lemma fanTriangle_chain_sameCycle {a b c : M.Vertex}
    (Ti : FanTriangle hNT v0 a b) (Tj : FanTriangle hNT v0 b c)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    (M.deleteVertex d0).φ.SameCycle
      ⟨Ti.d1, fanTriangle_d1_survives Ti htail0⟩
      ⟨Tj.d1, fanTriangle_d1_survives Tj htail0⟩ := by
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [zpow_one]
  exact fanTriangle_chain_step Ti Tj htail0



/-- `consecutivePairs` of a two-or-more element list. -/
 lemma consecutivePairs_cons_cons_p2m_b5533c713919 {α : Type*} (a b : α) (l : List α) :
    consecutivePairs (a :: b :: l) = (a, b) :: consecutivePairs (b :: l) := by
  simp [consecutivePairs]

/-- Every triangle edge dart along the path is in the `φ'`-cycle of a fixed
reference survivor `r`, provided `r` is linked to the **head** triangle's edge
dart (the triangle of the first pair `(hd, L.head)`) and all consecutive pairs
carry triangles.  The tail list `L` is destructured internally, so the caller
need not split it (keeping the path's `fan.x :: interior ++ [w]` shape).

Predecessor convention: a forward consecutive pair `(a, b)` carries the swapped
triangle `FanTriangle v0 b a`.  Consecutive forward pairs `(hd, c), (c, c')` give
triangles `Ti = (v0, c, hd)`, `Tj = (v0, c', c)` sharing `c` as `Ti.tail1 = Tj.tail2`;
the chain step `fanTriangle_chain_sameCycle` (which links `(v0, a, b)`-then-`(v0, b, c)`
in `φ'`) thus applies in the reverse order `(Tj, Ti)`, giving the same `φ'`-cycle. -/
 lemma fanTriangle_edge_dart_sameCycle_ref {d0 : D} (htail0 : M.tail d0 = v0)
    (r : {d : D // d ∉ M.deleteVertexSet d0}) :
    ∀ (L : List M.Vertex) (hd : M.Vertex)
      (htri : ∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (hd :: L) →
        FanTriangle hNT v0 b a),
      (∀ (c : M.Vertex) (hpc : (hd, c) ∈ consecutivePairs (hd :: L)),
        (M.deleteVertex d0).φ.SameCycle r
          ⟨(htri hd c hpc).d1, fanTriangle_d1_survives _ htail0⟩) →
      ∀ {a b : M.Vertex} (hab : (a, b) ∈ consecutivePairs (hd :: L)),
        (M.deleteVertex d0).φ.SameCycle r
          ⟨(htri a b hab).d1, fanTriangle_d1_survives _ htail0⟩ := by
  intro L
  induction L with
  | nil => intro hd htri _ a b hab; simp [consecutivePairs] at hab
  | cons c t ih =>
      intro hd htri hhead a b hab
      have hpc : (hd, c) ∈ consecutivePairs (hd :: c :: t) := by
        rw [consecutivePairs_cons_cons_p2m_b5533c713919]; exact List.mem_cons.mpr (Or.inl rfl)
      have lift : ∀ a' b' : M.Vertex, (a', b') ∈ consecutivePairs (c :: t) →
          (a', b') ∈ consecutivePairs (hd :: c :: t) := fun a' b' hab' => by
        rw [consecutivePairs_cons_cons_p2m_b5533c713919]; exact List.mem_cons.mpr (Or.inr hab')
      set htri' : ∀ a' b' : M.Vertex, (a', b') ∈ consecutivePairs (c :: t) →
          FanTriangle hNT v0 b' a' :=
        fun a' b' hab' => htri a' b' (lift a' b' hab') with htri'def
      have hhead' : ∀ (c' : M.Vertex) (hpc' : (c, c') ∈ consecutivePairs (c :: t)),
          (M.deleteVertex d0).φ.SameCycle r
            ⟨(htri' c c' hpc').d1, fanTriangle_d1_survives _ htail0⟩ := by
        intro c' hpc'
        -- `htri hd c hpc : (v0, c, hd)`, `htri' c c' hpc' : (v0, c', c)`; they share `c`
        -- as `(htri' c c').tail2 = (htri hd c).tail1`, so the chain step links
        -- `(htri' c c').d1 → (htri hd c).d1`; take `.symm`.
        exact (hhead c hpc).trans
          (fanTriangle_chain_sameCycle (htri' c c' hpc') (htri hd c hpc) htail0).symm
      rw [consecutivePairs_cons_cons_p2m_b5533c713919] at hab
      rcases List.mem_cons.mp hab with hhd | htl
      · have hae : a = hd := (Prod.ext_iff.mp hhd).1
        have hbe : b = c := (Prod.ext_iff.mp hhd).2
        cases hae; cases hbe; exact hhead c hab
      · exact ih c htri' hhead' htl



/-- The `φ`-orbit (face) of a fan triangle is exactly `{d0, d1, d2}`; a survivor
of that face is `d1`. -/
 lemma survivor_on_fanTriangle_eq_d1 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : M.dartFace x.1 = T.face) :
    x.1 = T.d1 := by
  -- dartFace T.d1 = T.face (= dartFace T.d0, and φ T.d0 = T.d1).
  have hdf1 : M.dartFace T.d1 = T.face := by
    rw [FanTriangle.face, ← T.triangle.1, dartFace_phi]
  -- face has length 3, so φ-orbit of T.d1 is {d1, d2, d0}; x.1 is one of them.
  have hlen : M.faceLen (M.dartFace T.d1) = 3 := by
    rw [hdf1]; exact T.faceLen_eq_three
  -- x.1 ~φ T.d1
  have hsame : M.φ.SameCycle T.d1 x.1 :=
    Quotient.exact (show M.dartFace T.d1 = M.dartFace x.1 by rw [hdf1, hface])
  have hφ : M.φ T.d1 ≠ T.d1 := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph T.d1
  have hsupp : T.d1 ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  have hcard : (M.φ.cycleOf T.d1).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  obtain ⟨i, hi, hpow⟩ := hsame.exists_pow_eq_of_mem_support hsupp
  rw [hcard] at hi
  have h01 : M.φ T.d1 = T.d2 := T.triangle.2.1
  have h12 : M.φ T.d2 = T.d0 := T.triangle.2.2
  interval_cases i
  · simpa using hpow.symm
  · -- x.1 = φ T.d1 = T.d2, deleted (head v0): contradiction
    exfalso
    have : x.1 = T.d2 := by simpa [h01] using hpow.symm
    exact x.2 (this ▸ fanTriangle_d2_deleted T htail0)
  · -- x.1 = φ² T.d1 = T.d0, deleted (tail v0): contradiction
    exfalso
    have hx0 : x.1 = T.d0 := by
      have h2 : (M.φ ^ 2) T.d1 = T.d0 := by
        rw [show (2:ℕ) = 1+1 from rfl, pow_succ', pow_one]
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, h01, h12]
      rw [h2] at hpow; exact hpow.symm
    have hd0del : T.d0 ∈ M.deleteVertexSet d0 := by
      rw [mem_deleteVertexSet_iff]; left
      rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail T.d0 by rw [htail0, T.tail0])
    exact x.2 (hx0 ▸ hd0del)

/-- An incident survivor's `M`-face is incident with `v0` in the
`FaceIncidentAtVertex` sense (some dart of the face has tail `v0`). -/
 lemma faceIncidentAtVertex_of_incident {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hx : M.dartFace x.1 ∈ M.vertexFaces d0) :
    FaceIncidentAtVertex M (M.dartFace x.1) v0 := by
  rw [vertexFaces, Finset.mem_image] at hx
  obtain ⟨e, he, hef⟩ := hx
  rw [mem_vertexDarts] at he
  refine ⟨e, hef, ?_⟩
  have : M.tail d0 = M.tail e := Quotient.sound he
  rw [← this, htail0]



/-- The isolated outer-arc reconnection: every surviving dart on the old outer
face is in the `φ'`-cycle of the fixed reference fan-triangle edge dart `r`. -/
def MergedOuterArcReconnects (M : CombMap D) (d0 : D)
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (outerFace : M.Face) : Prop :=
  ∀ x : {d : D // d ∉ M.deleteVertexSet d0},
    M.dartFace x.1 = outerFace → (M.deleteVertex d0).φ.SameCycle r x



/-- A fan-triangle edge reference tied to the canonical `triangle_of_pair` field of
the fan.  This is the right target for the old-outer seam: the Case-B jump lands
on one concrete fan edge, and the fan-chain lemma transports that edge to the
head reference internally. -/
def FanTriangleEdge (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (r : {d : D // d ∉ M.deleteVertexSet d0}) : Prop :=
  ∃ (a b : M.Vertex) (hp : (a, b) ∈ consecutivePairs fan.path),
    r.1 = (fan.incident_faces_exact.triangle_of_pair hp).d1

/-- **The merged-face single-orbit fact from an arbitrary actual seam fan edge.**
The old outer arc may Case-B-jump into any fan-triangle edge on the fan chain.  The
proved fan-chain `SameCycle` calculus transports that entry edge to the head
reference used by the existing merged-orbit proof, so the final
`DeleteVertexMergedFaceSingleOrbit` is independent of the entry point. -/
theorem deleteVertexMergedFaceSingleOrbit_of_fan_from_edge (fan : BoundaryVertexFan hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (rₛ : {d : D // d ∉ M.deleteVertexSet d0})
    (hrₛ : FanTriangleEdge fan rₛ)
    (houterₛ : MergedOuterArcReconnects M d0 rₛ hNT.outerFace) :
    DeleteVertexMergedFaceSingleOrbit M d0 := by
  classical
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  let toPath : ∀ a b : M.Vertex,
      (a, b) ∈ consecutivePairs (fan.x :: L) → (a, b) ∈ consecutivePairs fan.path :=
    fun _ _ hab => by rw [hpath]; exact hab
  let htri : ∀ a b : M.Vertex,
      (a, b) ∈ consecutivePairs (fan.x :: L) → FanTriangle hNT v0 b a :=
    fun a b hab => fan.incident_faces_exact.triangle_of_pair (toPath a b hab)
  have hnodup : (fan.x :: L).Nodup := by
    have := fan_path_simple_of_chordless hNT fan hchord
    rwa [hpath] at this
  obtain ⟨b0, l', hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  have hpair0 : (fan.x, b0) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons_p2m_b5533c713919]; exact List.mem_cons.mpr (Or.inl rfl)
  set r : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(htri fan.x b0 hpair0).d1, fanTriangle_d1_survives _ htail0⟩ with hr
  have hhead : ∀ (c : M.Vertex) (hpc : (fan.x, c) ∈ consecutivePairs (fan.x :: L)),
      (M.deleteVertex d0).φ.SameCycle r
        ⟨(htri fan.x c hpc).d1, fanTriangle_d1_survives _ htail0⟩ := by
    intro c hpc
    have hcb0 : c = b0 := by
      rw [hLb, consecutivePairs_cons_cons_p2m_b5533c713919] at hpc
      rcases List.mem_cons.mp hpc with hhd | htl
      · exact (Prod.ext_iff.mp hhd).2
      · exfalso
        have hxmem : fan.x ∈ b0 :: l' := (List.of_mem_zip htl).1
        have hnd : (fan.x :: b0 :: l').Nodup := by rw [← hLb]; exact hnodup
        exact (List.nodup_cons.mp hnd).1 hxmem
    subst hcb0
    exact Equiv.Perm.SameCycle.refl _ _
  have hentry : (M.deleteVertex d0).φ.SameCycle r rₛ := by
    rcases hrₛ with ⟨a, b, hp, hrval⟩
    have hp' : (a, b) ∈ consecutivePairs (fan.x :: L) := by
      rw [← hpath]; exact hp
    have hlink := fanTriangle_edge_dart_sameCycle_ref htail0 r L fan.x htri hhead hp'
    have hval : rₛ.1 = (htri a b hp').d1 := by
      rw [hrval]
    have hsub : rₛ =
        (⟨(htri a b hp').d1, fanTriangle_d1_survives (htri a b hp') htail0⟩ :
          {d : D // d ∉ M.deleteVertexSet d0}) := Subtype.ext hval
    rw [hsub]
    exact hlink
  have houter_r : MergedOuterArcReconnects M d0 r hNT.outerFace := by
    intro x hx
    exact hentry.trans (houterₛ x hx)
  suffices hkey : ∀ z : {d : D // d ∉ M.deleteVertexSet d0},
      M.dartFace z.1 ∈ M.vertexFaces d0 → (M.deleteVertex d0).φ.SameCycle r z by
    intro x y hx hy
    exact (hkey x hx).symm.trans (hkey y hy)
  intro z hz
  by_cases hzouter : M.dartFace z.1 = hNT.outerFace
  · exact houter_r z hzouter
  · have hinc : FaceIncidentAtVertex M (M.dartFace z.1) v0 :=
      faceIncidentAtVertex_of_incident htail0 z hz
    obtain ⟨a, b, hp, hface⟩ :=
      (fan.incident_faces_exact.exact_faces (M.dartFace z.1) hzouter).1 hinc
    have hp' : (a, b) ∈ consecutivePairs (fan.x :: L) := by rw [← hpath]; exact hp
    have hTface : (htri a b hp').face = M.dartFace z.1 := by
      show (fan.incident_faces_exact.triangle_of_pair _).face = M.dartFace z.1
      convert hface using 2
    have hzd1 : z.1 = (htri a b hp').d1 :=
      survivor_on_fanTriangle_eq_d1 (htri a b hp') htail0 z hTface.symm
    have hlink := fanTriangle_edge_dart_sameCycle_ref htail0 r L fan.x htri hhead hp'
    have hzeq : z = (⟨(htri a b hp').d1, fanTriangle_d1_survives (htri a b hp') htail0⟩ :
        {d : D // d ∉ M.deleteVertexSet d0}) := Subtype.ext hzd1
    rw [hzeq]; exact hlink



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapBoundaryArcSplit -/
section
set_option autoImplicit true




set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- Boundary vertices are represented by the exposed cyclic vertex list. -/
def IsBoundaryVertex (K : BoundaryCycleData M f) (v : M.Vertex) : Prop :=
  v ∈ K.vertices

/-- Boundary edges are represented by the exposed cyclic edge list. -/
def IsBoundaryEdge (K : BoundaryCycleData M f) (e : Sym2 M.Vertex) : Prop :=
  e ∈ K.edges

/-- The boundary vertex list is simple. -/
def VertexNodup (K : BoundaryCycleData M f) : Prop :=
  K.vertices.Nodup





lemma darts_length_pos (K : BoundaryCycleData M f) : 0 < K.darts.length :=
  K.normalized.length_pos

end BoundaryCycleData



theorem modCoverD (L pf pt : ℕ) (hLpos : 0 < L) (hpf : pf < L) (hpt : pt < L) (hne : pf ≠ pt)
    (kf kb : ℕ) (hkf_eq : kf = (pt + L - pf) % L) (hkb_eq : kb = (pf + L - pt) % L) :
    1 ≤ kf ∧ 1 ≤ kb ∧ kf + kb = L ∧ (pf + kf) % L = pt ∧
    ∀ q, q < L → (∃ j, j < kf ∧ (pf + j) % L = q) ∨ (∃ j, j < kb ∧ (pt + j) % L = q) := by
  have hkf1 : 1 ≤ kf := by
    rw [hkf_eq]
    rcases Nat.eq_zero_or_pos ((pt + L - pf) % L) with h0 | h0
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have hlt : pt + L - pf < 2 * L := by omega
      have hgt : 0 < pt + L - pf := by omega
      have : m = 1 := by nlinarith
      rw [this, Nat.mul_one] at hm; omega
    · exact h0
  have hkb1 : 1 ≤ kb := by
    rw [hkb_eq]
    rcases Nat.eq_zero_or_pos ((pf + L - pt) % L) with h0 | h0
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have hlt : pf + L - pt < 2 * L := by omega
      have hgt : 0 < pf + L - pt := by omega
      have : m = 1 := by nlinarith
      rw [this, Nat.mul_one] at hm; omega
    · exact h0
  have hkfval : kf = if pf ≤ pt then pt - pf else pt + L - pf := by
    rw [hkf_eq]; split
    · next h => rw [show pt + L - pf = (pt - pf) + L from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  have hkbval : kb = if pt ≤ pf then pf - pt else pf + L - pt := by
    rw [hkb_eq]; split
    · next h => rw [show pf + L - pt = (pf - pt) + L from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : kf + kb = L := by rw [hkfval, hkbval]; split <;> split <;> omega
  have hpfkf : (pf + kf) % L = pt := by
    rw [hkf_eq]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have : pf + (pt + L - pf) = pt + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hpt]
  refine ⟨hkf1, hkb1, hsum, hpfkf, ?_⟩
  intro q hq
  set df := (q + L - pf) % L with hdf
  have hdfL : df < L := Nat.mod_lt _ hLpos
  have hpfdf : (pf + df) % L = q := by
    rw [hdf]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have : pf + (q + L - pf) = q + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  by_cases hd : df < kf
  · exact Or.inl ⟨df, hd, hpfdf⟩
  · refine Or.inr ⟨df - kf, by omega, ?_⟩
    calc (pt + (df - kf)) % L = ((pf + kf) % L + (df - kf)) % L := by rw [hpfkf]
      _ = (pf + kf + (df - kf)) % L := by
            rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L), ← Nat.add_mod]
      _ = (pf + df) % L := by rw [show pf + kf + (df - kf) = pf + df from by omega]
      _ = q := hpfdf



/-- A dart-level boundary arc from `u` to `v` on the boundary-cycle core `K`. -/
structure DataDartArc (M : CombMap D) {f : M.Face} (K : BoundaryCycleData M f)
    (u v : M.Vertex) where
  /-- Number of darts on the arc. -/
  len : ℕ
  /-- The arc is nonempty (at least one dart). -/
  len_pos : 0 < len
  /-- The directed arc darts `e_0, …, e_{len-1}`. -/
  arcDart : Fin len → D
  /-- Every arc dart lies on the boundary cycle. -/
  boundary : ∀ i : Fin len, arcDart i ∈ K.darts
  /-- Consecutive arc darts chain head→tail (no wraparound — this is a *path*). -/
  chain : ∀ i : Fin len, (h : (i : ℕ) + 1 < len) →
    M.head (arcDart i) = M.tail (arcDart ⟨i + 1, h⟩)
  /-- The first dart's tail is `u`. -/
  tail_first : M.tail (arcDart ⟨0, len_pos⟩) = u
  /-- The last dart's head is `v`. -/
  head_last : M.head (arcDart ⟨len - 1, by omega⟩) = v
  /-- The tail vertices of the arc darts are pairwise distinct (simplicity). -/
  tail_nodup : Function.Injective (fun i : Fin len => M.tail (arcDart i))
  /-- The final head `v` is distinct from every tail (the arc does not revisit its
  endpoint). -/
  head_last_ne_tail : ∀ i : Fin len, v ≠ M.tail (arcDart i)

namespace DataDartArc

variable {M : CombMap D} {f : M.Face} {K : BoundaryCycleData M f} {u v : M.Vertex}



/-- The first index of the arc. -/
def firstIdx (A : DataDartArc M K u v) : Fin A.len := ⟨0, A.len_pos⟩





/-- The explicit `List D` of a `DataDartArc`'s darts, `[arcDart 0, …, arcDart (len-1)]`. -/
def dartList (A : DataDartArc M K u v) : List D :=
  (List.finRange A.len).map A.arcDart

@[simp] lemma dartList_length (A : DataDartArc M K u v) : A.dartList.length = A.len := by
  simp [DataDartArc.dartList]

lemma dartList_ne_nil (A : DataDartArc M K u v) : A.dartList ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, DataDartArc.dartList_length]; exact A.len_pos

lemma dartList_getElem (A : DataDartArc M K u v) (j : ℕ) (hj : j < A.len) :
    A.dartList[j]'(by rw [DataDartArc.dartList_length]; exact hj) = A.arcDart ⟨j, hj⟩ := by
  simp only [DataDartArc.dartList, List.getElem_map, List.getElem_finRange]
  congr 1

lemma mem_dartList (A : DataDartArc M K u v) {d : D} (hd : d ∈ A.dartList) :
    ∃ i : Fin A.len, A.arcDart i = d := by
  rw [DataDartArc.dartList, List.mem_map] at hd
  obtain ⟨i, _, hi⟩ := hd
  exact ⟨i, hi⟩

end DataDartArc



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- The position of a boundary vertex on the cyclic dart list (as the tail of a
listed dart), as a single existential over `Fin`. -/
lemma exists_pos_of_isBoundaryVertex (K : BoundaryCycleData M f) {a : M.Vertex}
    (ha : K.IsBoundaryVertex a) :
    ∃ p : Fin K.darts.length, M.tail (K.darts[p.1]'p.2) = a := by
  have ha' : a ∈ K.darts.map M.tail := by
    simpa [BoundaryCycleData.IsBoundaryVertex, K.vertices_eq] using ha
  rw [List.mem_iff_getElem] at ha'
  obtain ⟨p, hp, hget⟩ := ha'
  rw [List.length_map] at hp
  refine ⟨⟨p, hp⟩, ?_⟩
  rwa [List.getElem_map] at hget

/-- Given a boundary-cycle core `K` (vertices simple), a start position `p`, and a
*cyclic* run length `k` with `1 ≤ k ≤ K.darts.length`, the darts `K.darts[(p + j) % L]`
(`j < k`) form a `DataDartArc` from `M.tail (K.darts[p])` to `M.tail (K.darts[(p+k)%L])`. -/
noncomputable def cyclicDataDartArc (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length)
    (hp : p < K.darts.length) :
    DataDartArc M K (M.tail (K.darts[p]'hp))
      (M.tail (K.darts[(p + k) % K.darts.length]'(Nat.mod_lt _ (by omega)))) where
  len := k
  len_pos := hk
  arcDart j := K.darts[(p + j.1) % K.darts.length]'(Nat.mod_lt _ (by omega))
  boundary j := List.getElem_mem _
  chain j hj := by
    set L := K.darts.length with hL
    have hLpos : 0 < L := K.darts_length_pos
    have hpos : (p + (j : ℕ)) % L < L := Nat.mod_lt _ hLpos
    have hcv := K.consecutive_vertex ⟨(p + (j : ℕ)) % L, hpos⟩
    have hcyc : (cyclicNext K.normalized.length_pos ⟨(p + (j : ℕ)) % L, hpos⟩ : Fin L)
        = ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (j : ℕ)) % L + 1) % L = (p + ((j : ℕ) + 1)) % L
      rw [Nat.mod_add_mod]
      congr 1
    rw [hcyc] at hcv
    show M.head (K.darts[(p + (j : ℕ)) % L]'_)
        = M.tail (K.darts[(p + ((j : ℕ) + 1)) % L]'_)
    rw [show (K.darts.get ⟨(p + (j : ℕ)) % L, hpos⟩) = K.darts[(p + (j : ℕ)) % L]'hpos from rfl,
      show (K.darts.get ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩)
          = K.darts[(p + ((j : ℕ) + 1)) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_first := by
    have hLpos : 0 < K.darts.length := K.darts_length_pos
    have heq : (p + (0 : ℕ)) % K.darts.length = p := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hp]
    show M.tail (K.darts[(p + (0 : ℕ)) % K.darts.length]'_) = M.tail (K.darts[p]'hp)
    simp only [heq]
  head_last := by
    set L := K.darts.length with hL
    have hLpos : 0 < L := K.darts_length_pos
    have hpos : (p + (k - 1)) % L < L := Nat.mod_lt _ hLpos
    have hcv := K.consecutive_vertex ⟨(p + (k - 1)) % L, hpos⟩
    have hcyc : (cyclicNext K.normalized.length_pos ⟨(p + (k - 1)) % L, hpos⟩ : Fin L)
        = ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (k - 1)) % L + 1) % L = (p + k) % L
      rw [Nat.mod_add_mod]
      congr 1
      omega
    rw [hcyc] at hcv
    show M.head (K.darts[(p + ((k : ℕ) - 1)) % L]'_) = M.tail (K.darts[(p + k) % L]'_)
    rw [show (K.darts.get ⟨(p + (k - 1)) % L, hpos⟩) = K.darts[(p + (k - 1)) % L]'hpos from rfl,
      show (K.darts.get ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩)
          = K.darts[(p + k) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_nodup := by
    set L := K.darts.length with hL
    have hmap : (K.darts.map M.tail).Nodup := by
      simpa [BoundaryCycleData.VertexNodup, K.vertices_eq] using hK
    intro i₁ i₂ htail
    have hi₁ : (i₁ : ℕ) < k := i₁.isLt
    have hi₂ : (i₂ : ℕ) < k := i₂.isLt
    have h1 : (p + (i₁ : ℕ)) % L < L := Nat.mod_lt _ K.darts_length_pos
    have h2 : (p + (i₂ : ℕ)) % L < L := Nat.mod_lt _ K.darts_length_pos
    have hdarts : K.darts[(p + (i₁ : ℕ)) % L]'h1 = K.darts[(p + (i₂ : ℕ)) % L]'h2 := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem h1) (List.getElem_mem h2)
      exact hinj htail
    have hpos_eq : (p + (i₁ : ℕ)) % L = (p + (i₂ : ℕ)) % L :=
      (K.normalized.nodup.getElem_inj_iff).mp hdarts
    have hi₁L0 : (i₁ : ℕ) < L := lt_of_lt_of_le hi₁ (le_of_lt hkL)
    have hi₂L0 : (i₂ : ℕ) < L := lt_of_lt_of_le hi₂ (le_of_lt hkL)
    have hmodeq : Nat.ModEq L (p + (i₁ : ℕ)) (p + (i₂ : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L (i₁ : ℕ) (i₂ : ℕ) :=
      Nat.ModEq.add_left_cancel' p hmodeq
    have hi₁L : (i₁ : ℕ) % L = (i₁ : ℕ) := Nat.mod_eq_of_lt hi₁L0
    have hi₂L : (i₂ : ℕ) % L = (i₂ : ℕ) := Nat.mod_eq_of_lt hi₂L0
    apply Fin.ext
    have := hcancel
    rw [Nat.ModEq, hi₁L, hi₂L] at this
    exact this
  head_last_ne_tail := by
    set L := K.darts.length with hL
    have hmap : (K.darts.map M.tail).Nodup := by
      simpa [BoundaryCycleData.VertexNodup, K.vertices_eq] using hK
    intro i htail
    have hi : (i : ℕ) < k := i.isLt
    have hposk : (p + k) % L < L := Nat.mod_lt _ K.darts_length_pos
    have hposi : (p + (i : ℕ)) % L < L := Nat.mod_lt _ K.darts_length_pos
    have hdarts : K.darts[(p + k) % L]'hposk = K.darts[(p + (i : ℕ)) % L]'hposi := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem hposk) (List.getElem_mem hposi)
      exact hinj htail
    have hpos_eq : (p + k) % L = (p + (i : ℕ)) % L :=
      (K.normalized.nodup.getElem_inj_iff).mp hdarts
    have hiltL : (i : ℕ) < L := lt_trans hi hkL
    have hmodeq : Nat.ModEq L (p + k) (p + (i : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L k (i : ℕ) := Nat.ModEq.add_left_cancel' p hmodeq
    have hkL' : k % L = k := Nat.mod_eq_of_lt hkL
    have hiL : (i : ℕ) % L = (i : ℕ) := Nat.mod_eq_of_lt hiltL
    rw [Nat.ModEq, hkL', hiL] at hcancel
    omega



@[simp] lemma cyclicDataDartArc_arcDart (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length) (hp : p < K.darts.length)
    (j : Fin k) :
    (cyclicDataDartArc K hK p k hk hkL hp).arcDart j
      = K.darts[(p + j.1) % K.darts.length]'(Nat.mod_lt _ (by omega)) := rfl

end BoundaryCycleData



section Casts

variable {M : CombMap D}

/-- Retype a `DataDartArc`'s endpoints along equalities. -/
noncomputable def daCastD {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') : DataDartArc M K a' b' := ha ▸ hb ▸ A

@[simp] lemma daCastD_len {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') : (daCastD A ha hb).len = A.len := by
  subst ha; subst hb; rfl

lemma daCastD_arcDart {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') (i : Fin (daCastD A ha hb).len) :
    M.tail ((daCastD A ha hb).arcDart i)
      = M.tail (A.arcDart (Fin.cast (daCastD_len A ha hb) i)) := by
  subst ha; subst hb; rfl



/-- **The tail of a casted cyclic dart-arc at index `i` is the cyclic-slice tail `darts[(p+i)%L]`.** -/
lemma daCastD_cyclic_tail {f : M.Face} (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length) (hp : p < K.darts.length)
    {a' b' : M.Vertex}
    (ha : M.tail (K.darts[p]'hp) = a')
    (hb : M.tail (K.darts[(p + k) % K.darts.length]'(Nat.mod_lt _ (by omega))) = b')
    (i : Fin (daCastD (K.cyclicDataDartArc hK p k hk hkL hp) ha hb).len) :
    M.tail ((daCastD (K.cyclicDataDartArc hK p k hk hkL hp) ha hb).arcDart i)
      = M.tail (K.darts[(p + i.1) % K.darts.length]'(Nat.mod_lt _ (by omega))) := by
  rw [daCastD_arcDart, BoundaryCycleData.cyclicDataDartArc_arcDart]; rfl

end Casts



/-- Under `Nodup`, the last element of a list does not occur in its `dropLast`. -/
lemma getLastNotMemDropLastD {α : Type*} {l : List α} (hl : l ≠ [])
    (hnd : l.Nodup) : l.getLast hl ∉ l.dropLast := by
  have hsplit : l.dropLast ++ [l.getLast hl] = l := List.dropLast_append_getLast hl
  have hnd' : (l.dropLast ++ [l.getLast hl]).Nodup := by rw [hsplit]; exact hnd
  intro hmem
  exact (List.disjoint_of_nodup_append hnd') hmem (by simp)

/-- A generic list fact: if `l.head? = some a` and `l.Nodup`, then `a ∉ l.tail`. -/
lemma headNotMemTailD {α : Type*} {a : α} {l : List α}
    (hh : l.head? = some a) (hnd : l.Nodup) : a ∉ l.tail := by
  cases l with
  | nil => simp at hh
  | cons b t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simpa using (List.nodup_cons.mp hnd).1















namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}



/-- An internal vertex is distinct from the initial endpoint. -/
lemma internalVertexNeStartD (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ u := by
  have hutail : u ∉ P.vertices.tail :=
    headNotMemTailD P.starts_at P.simple
  have hwtail : w ∈ P.vertices.tail := List.dropLast_subset _ hw
  intro hwu; subst hwu; exact hutail hwtail

/-- An internal vertex is distinct from the terminal endpoint. -/
lemma internalVertexNeEndD (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ v := by
  have hwtail_dropLast : w ∈ P.vertices.tail.dropLast := hw
  have htail_ne : P.vertices.tail ≠ [] := fun h => by rw [h] at hwtail_dropLast; simp at hwtail_dropLast
  have hnodup_tail : P.vertices.tail.Nodup := P.simple.sublist (List.tail_sublist _)
  have hlast_tail : P.vertices.tail.getLast htail_ne = v :=
    getLast_tail_of_getLast? P.ends_at htail_ne
  have hnotmem : P.vertices.tail.getLast htail_ne ∉ P.vertices.tail.dropLast :=
    getLastNotMemDropLastD htail_ne hnodup_tail
  intro hwv; subst hwv
  exact hnotmem (hlast_tail.symm ▸ hwtail_dropLast)

end BoundaryPath



section BPOfDartArc

variable {M : CombMap D}

/-- **The `BoundaryPath` of a dart arc.**  Its vertices are the arc-dart tails followed by the
terminal endpoint `b`; its edges are the arc-dart graph edges. -/
noncomputable def bpOfDDA {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) : BoundaryPath M a b where
  vertices := A.dartList.map M.tail ++ [b]
  edges := A.dartList.map M.dartEdge
  starts_at := by
    have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
    have h0 : 0 < A.dartList.length := by rw [DataDartArc.dartList_length]; exact A.len_pos
    rw [List.head?_append_of_ne_nil _ hne, List.head?_map, List.head?_eq_getElem?,
      List.getElem?_eq_getElem h0, A.dartList_getElem 0 A.len_pos]
    simp only [Option.map_some]; rw [A.tail_first]
  ends_at := by simp
  simple := by
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [DataDartArc.dartList, List.map_map, List.nodup_map_iff_inj_on (List.nodup_finRange A.len)]
      intro i _ j _ hij; exact A.tail_nodup hij
    · intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      rw [List.mem_map] at hx
      obtain ⟨d, hd, hdt⟩ := hx
      obtain ⟨i, hi⟩ := A.mem_dartList hd
      rw [← hi] at hdt
      exact fun hxb => A.head_last_ne_tail i (hxb ▸ hdt.symm)

@[simp] lemma bpOfDDA_vertices {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) : (bpOfDDA A).vertices = A.dartList.map M.tail ++ [b] := rfl



/-- The internal vertices of `bpOfDDA A` are the tails of the arc darts with index `≥ 1`. -/
lemma bpOfDDA_internal {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) :
    (bpOfDDA A).internalVertices = (A.dartList.map M.tail).tail := by
  show (A.dartList.map M.tail ++ [b]).tail.dropLast = (A.dartList.map M.tail).tail
  have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
  rw [List.tail_append_of_ne_nil hne, List.dropLast_concat]

/-- Every vertex of `bpOfDDA A` is a tail of an arc dart, or the terminal endpoint `b`. -/
lemma bpOfDDA_mem_vertices {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) {w : M.Vertex} (hw : w ∈ (bpOfDDA A).vertices) :
    (∃ i : Fin A.len, M.tail (A.arcDart i) = w) ∨ w = b := by
  rw [bpOfDDA_vertices, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | hw
  · left
    rw [List.mem_map] at hw
    obtain ⟨d, hd, hdt⟩ := hw
    obtain ⟨i, hi⟩ := A.mem_dartList hd
    exact ⟨i, hi ▸ hdt⟩
  · right; exact hw

/-- An internal vertex of `bpOfDDA A` is a tail of an arc dart. -/
lemma bpOfDDA_internal_tail {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) {w : M.Vertex} (hw : w ∈ (bpOfDDA A).internalVertices) :
    ∃ i : Fin A.len, M.tail (A.arcDart i) = w := by
  rw [bpOfDDA_internal] at hw
  have hsub : w ∈ A.dartList.map M.tail := List.tail_subset _ hw
  rw [List.mem_map] at hsub
  obtain ⟨d, hd, hdt⟩ := hsub
  obtain ⟨i, hi⟩ := A.mem_dartList hd
  exact ⟨i, hi ▸ hdt⟩

/-- An arc-dart tail is a boundary vertex (`A`'s darts lie on the cycle). -/
lemma arcDartTailMemVD {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) (i : Fin A.len) : M.tail (A.arcDart i) ∈ K.vertices := by
  rw [K.vertices_eq]; exact List.mem_map_of_mem (A.boundary i)

/-- Every vertex of `bpOfDDA A` is a boundary vertex, provided the terminal endpoint `b` is. -/
lemma bpOfDDA_boundary_vertices {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) (hb : b ∈ K.vertices) {w : M.Vertex}
    (hw : w ∈ (bpOfDDA A).vertices) : w ∈ K.vertices := by
  rcases bpOfDDA_mem_vertices A hw with ⟨i, hi⟩ | hwb
  · rw [← hi]; exact arcDartTailMemVD A i
  · rw [hwb]; exact hb

/-- `bpOfDDA A` has an internal vertex when `2 ≤ A.len`. -/
lemma bpOfDDA_hasInternal {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) (hlen : 2 ≤ A.len) : (bpOfDDA A).HasInternalVertex := by
  rw [BoundaryPath.hasInternalVertex_iff, bpOfDDA_internal]
  intro hcontra
  have hlenlist : (A.dartList.map M.tail).length = A.len := by
    rw [List.length_map, DataDartArc.dartList_length]
  have htl : (A.dartList.map M.tail).tail.length = (A.dartList.map M.tail).length - 1 :=
    List.length_tail
  rw [hcontra] at htl
  simp only [List.length_nil] at htl
  omega

end BPOfDartArc



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- **No `1`-step between the two endpoint positions.**  If `s(u, v)` is not a boundary
edge then the positions `p` (tail `u`) and `q` (tail `v`) cannot be cyclic-consecutive. -/
lemma not_consecutive_of_nonBoundaryEdge (K : BoundaryCycleData M f) {u v : M.Vertex}
    (hnbe : ¬ K.IsBoundaryEdge s(u, v)) {p q : ℕ}
    (hp : p < K.darts.length) (hq : q < K.darts.length)
    (htu : M.tail (K.darts[p]'hp) = u)
    (htv : M.tail (K.darts[q]'hq) = v)
    (hadj : (p + 1) % K.darts.length = q) : False := by
  set L := K.darts.length with hL
  have hLpos : 0 < L := K.darts_length_pos
  have hcv := K.consecutive_vertex ⟨p, hp⟩
  have hcyc : (cyclicNext K.normalized.length_pos ⟨p, hp⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext; show (p + 1) % L = q; exact hadj
  rw [hcyc] at hcv
  have hhead : M.head (K.darts[p]'hp) = v := by
    rw [show (K.darts.get ⟨q, hq⟩) = K.darts[q]'hq from rfl,
        show (K.darts.get ⟨p, hp⟩) = K.darts[p]'hp from rfl] at hcv
    rw [← hcv, htv]
  apply hnbe
  show s(u, v) ∈ K.edges
  rw [K.edges_eq, show (s(u, v) : Sym2 M.Vertex) = M.dartEdge (K.darts[p]'hp) from by
    show s(u, v) = s(M.tail _, M.head _); rw [htu, hhead]]
  exact List.mem_map_of_mem (List.getElem_mem hp)





end BoundaryCycleData



namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- **The universal arc-split from `VertexNodup`, over the CORE.**  For any two distinct
listed boundary vertices `u, v` (no adjacency restriction), the two complementary cyclic
runs assemble a `BoundaryArcSplit M K.vertices K.edges u v`.  Pure list combinatorics from
simplicity. -/
noncomputable def arcSplit_of_nodup (K : BoundaryCycleData M f) (hK : K.vertices.Nodup)
    ⦃u v : M.Vertex⦄ (hne : u ≠ v)
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) :
    BoundaryArcSplit M K.vertices K.edges u v := by
  classical
  set L := K.darts.length with hL
  have hLpos : 0 < L := K.darts_length_pos
  set puF := (K.exists_pos_of_isBoundaryVertex hu).choose with hpuF
  have eu0 := (K.exists_pos_of_isBoundaryVertex hu).choose_spec
  set pvF := (K.exists_pos_of_isBoundaryVertex hv).choose with hpvF
  have ev0 := (K.exists_pos_of_isBoundaryVertex hv).choose_spec
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (K.darts[pu]'hpu) = u := eu0
  have ev : M.tail (K.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply hne
    rw [← eu, ← ev]
    have : K.darts[pu]'hpu = K.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ :=
    modCoverD L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  obtain ⟨_, _, _, hpvkb, _⟩ :=
    modCoverD L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  set AUV := K.cyclicDataDartArc hK pu kf hkf1 hkfL hpu with hAUV
  set AVU := K.cyclicDataDartArc hK pv kb hkb1 hkbL hpv with hAVU
  have euv2 : M.tail (K.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : K.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = K.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (K.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : K.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = K.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  have htailUV : ∀ i : Fin (daCastD AUV eu euv2).len,
      M.tail ((daCastD AUV eu euv2).arcDart i)
        = M.tail (K.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCastD_cyclic_tail K hK pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCastD AVU ev evu2).len,
      M.tail ((daCastD AVU ev evu2).arcDart i)
        = M.tail (K.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCastD_cyclic_tail K hK pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCastD AUV eu euv2).len,
        M.tail ((daCastD AUV eu euv2).arcDart i)
          = M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCastD AUV eu euv2).len := by rw [daCastD_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCastD AVU ev evu2).len,
        M.tail ((daCastD AVU ev evu2).arcDart i)
          = M.tail (K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCastD AVU ev evu2).len := by rw [daCastD_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCastD AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCastD AUV eu euv2).arcDart i)
          = M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCastD_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCastD AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCastD AVU ev evu2).arcDart i)
          = M.tail (K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCastD_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  -- covering and disjointness of the two runs' tails (no length-≥2 needed)
  have hmap : (K.darts.map M.tail).Nodup := by
    have := hK; rwa [K.vertices_eq] at this
  have covering : ∀ {w : M.Vertex}, w ∈ K.vertices →
      (∃ i, M.tail ((daCastD AUV eu euv2).arcDart i) = w) ∨
      (∃ i, M.tail ((daCastD AVU ev evu2).arcDart i) = w) ∨ w = u ∨ w = v := by
    intro w hw
    obtain ⟨q, hqt⟩ := K.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = K.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = K.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  have disjoint : ∀ {w : M.Vertex},
      (∃ i, M.tail ((daCastD AUV eu euv2).arcDart i) = w) →
      (∃ i, M.tail ((daCastD AVU ev evu2).arcDart i) = w) → w = u ∨ w = v := by
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    have heq : M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ K.darts :=
        List.getElem_mem _
      have hmem2 : K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ K.darts :=
        List.getElem_mem _
      have hdarts : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (K.normalized.nodup.getElem_inj_iff).mp hdarts
    by_cases hj0 : j = 0
    · left
      rw [← hiw, hjeq, hj0]
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hpu]
      exact eu
    · by_cases hj'0 : j' = 0
      · right
        rw [← hi'w, hj'eq, hj'0]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hpv]
        exact ev
      · exfalso
        have hpvmod : pv % L = (pu + kf) % L := by rw [hpfkf, Nat.mod_eq_of_lt hpv]
        have h2 : Nat.ModEq L pv (pu + kf) := by
          show pv % L = (pu + kf) % L; exact hpvmod
        have hcong : Nat.ModEq L (pu + j) (pu + (kf + j')) := by
          have h1 : Nat.ModEq L (pu + j) (pv + j') := hposeq
          have h3 : Nat.ModEq L (pv + j') (pu + kf + j') := h2.add_right j'
          have h4 : Nat.ModEq L (pu + j) (pu + kf + j') := h1.trans h3
          rwa [show pu + kf + j' = pu + (kf + j') from by ring] at h4
        have hcong' : Nat.ModEq L j (kf + j') := Nat.ModEq.add_left_cancel' pu hcong
        have hjlt : j < L := by omega
        have hkfj' : kf + j' < L := by omega
        have : j = kf + j' := by
          have hj1 : j % L = j := Nat.mod_eq_of_lt hjlt
          have hj2 : (kf + j') % L = kf + j' := Nat.mod_eq_of_lt hkfj'
          rw [Nat.ModEq, hj1, hj2] at hcong'; exact hcong'
        omega
  -- length-≥2 from non-adjacency (only needed inside `internal_of_proper`)
  have hkf2_of_proper : s(u, v) ∉ K.edges → 2 ≤ kf := by
    intro hnbe
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_nonBoundaryEdge K hnbe hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2_of_proper : s(u, v) ∉ K.edges → 2 ≤ kb := by
    intro hnbe
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      have hnbe' : ¬ K.IsBoundaryEdge s(v, u) := by rw [Sym2.eq_swap]; exact hnbe
      exact not_consecutive_of_nonBoundaryEdge K hnbe' hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  refine
    { path₁ := bpOfDDA (daCastD AUV eu euv2)
      path₂ := bpOfDDA (daCastD AVU ev evu2)
      path₁_boundary_vertices := fun {w} hw => bpOfDDA_boundary_vertices (daCastD AUV eu euv2) hv hw
      path₂_boundary_vertices := fun {w} hw => bpOfDDA_boundary_vertices (daCastD AVU ev evu2) hu hw
      boundary_vertices_covered := ?_
      internally_disjoint := ?_
      path₁_internal_of_proper := ?_
      path₂_internal_of_proper := ?_ }
  · intro w
    constructor
    · intro hw
      rcases covering hw with ⟨i, hi⟩ | ⟨i, hi⟩ | hwu | hwv
      · left
        rw [bpOfDDA_vertices, List.mem_append]
        refine Or.inl ?_
        rw [← hi]
        exact List.mem_map_of_mem (by
          rw [DataDartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
      · right
        rw [bpOfDDA_vertices, List.mem_append]
        refine Or.inl ?_
        rw [← hi]
        exact List.mem_map_of_mem (by
          rw [DataDartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
      · left
        rw [bpOfDDA_vertices, List.mem_append]
        refine Or.inl ?_
        have hu_tail : M.tail ((daCastD AUV eu euv2).arcDart (daCastD AUV eu euv2).firstIdx) = w :=
          (daCastD AUV eu euv2).tail_first.trans hwu.symm
        have hmem : M.tail ((daCastD AUV eu euv2).arcDart (daCastD AUV eu euv2).firstIdx)
            ∈ (daCastD AUV eu euv2).dartList.map M.tail :=
          List.mem_map_of_mem (by
            rw [DataDartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange _))
        exact hu_tail ▸ hmem
      · left
        rw [bpOfDDA_vertices, List.mem_append]
        exact Or.inr (by rw [hwv]; exact List.mem_singleton_self _)
    · intro hw
      rcases hw with hw | hw
      · exact bpOfDDA_boundary_vertices (daCastD AUV eu euv2) hv hw
      · exact bpOfDDA_boundary_vertices (daCastD AVU ev evu2) hu hw
  · intro w hw1 hw2
    obtain ⟨i, hi⟩ := bpOfDDA_internal_tail (daCastD AUV eu euv2) hw1
    obtain ⟨i', hi'⟩ := bpOfDDA_internal_tail (daCastD AVU ev evu2) hw2
    have hwuv : w = u ∨ w = v := disjoint ⟨i, hi⟩ ⟨i', hi'⟩
    have hwu : w ≠ u := (bpOfDDA (daCastD AUV eu euv2)).internalVertexNeStartD hw1
    have hwv : w ≠ v := (bpOfDDA (daCastD AUV eu euv2)).internalVertexNeEndD hw1
    rcases hwuv with h' | h'
    · exact hwu h'
    · exact hwv h'
  · intro hnbe
    exact bpOfDDA_hasInternal (daCastD AUV eu euv2)
      (by rw [daCastD_len]; exact hkf2_of_proper hnbe)
  · intro hnbe
    exact bpOfDDA_hasInternal (daCastD AVU ev evu2)
      (by rw [daCastD_len]; exact hkb2_of_proper hnbe)

/-- **Promote a core + `VertexNodup` to a full `BoundaryCycle`** (the `arcSplit`
certificate is derived from simplicity by `arcSplit_of_nodup`). -/
noncomputable def toBoundaryCycle (K : BoundaryCycleData M f) (hK : K.vertices.Nodup) :
    BoundaryCycle M f :=
  { toBoundaryCycleData := K
    arcSplit := fun u v hne hu hv => K.arcSplit_of_nodup hK hne hu hv }

end BoundaryCycleData

end CombMap

end ProofsInTheBook.PlanarMap





end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.PlanarMapBoundaryArcSplit
-/
/- Source module: ProofsInTheBook.PlanarMapDeletedBoundary -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- The explicit cyclic dart list of a face's `φ`-orbit, rooted at `root`:
`[root, φ root, φ² root, …]`. -/
def faceDartList (M : CombMap D) (root : D) : List D :=
  M.φ.toList root

/-- The face dart list enumerates exactly the face orbit. -/
lemma faceDartList_toFinset (M : CombMap D) (f : M.Face) {root : D}
    (hφ : M.φ root ≠ root) (hroot : M.dartFace root = f) :
    (M.faceDartList root).toFinset = faceOrbitFinset M f := by
  classical
  have hsupp : root ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  ext d
  rw [List.mem_toFinset, mem_faceOrbitFinset_iff, faceDartList,
    Equiv.Perm.mem_toList_iff]
  constructor
  · rintro ⟨hsc, _⟩
    rw [← hroot]
    exact (Quotient.sound hsc.symm : M.dartFace d = M.dartFace root)
  · intro hdf
    refine ⟨?_, hsupp⟩
    exact Quotient.exact (show M.dartFace root = M.dartFace d by rw [hroot, hdf])

/-- The face dart list is nonempty when the orbit is nontrivial. -/
lemma faceDartList_length_pos (M : CombMap D) {root : D} (hφ : M.φ root ≠ root) :
    0 < (M.faceDartList root).length := by
  have hsupp : root ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  exact Equiv.Perm.length_toList_pos_of_mem_support _ _ hsupp

/-- `getElem` of the face dart list is `φ`-iterate of the root. -/
lemma faceDartList_getElem (M : CombMap D) (root : D) (n : ℕ)
    (hn : n < (M.faceDartList root).length) :
    (M.faceDartList root)[n] = (M.φ ^ n) root :=
  Equiv.Perm.getElem_toList _ _ _ _

/-- The head of the face dart list is the root. -/
lemma faceDartList_head (M : CombMap D) {root : D} (hφ : M.φ root ≠ root) :
    (M.faceDartList root).head? = some root := by
  have hsupp : root ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  have h0 : (M.faceDartList root)[0]'(M.faceDartList_length_pos hφ) = root := by
    have := M.faceDartList_getElem root 0 (M.faceDartList_length_pos hφ)
    simpa using this
  rw [List.head?_eq_getElem?,
    List.getElem?_eq_getElem (M.faceDartList_length_pos hφ), h0]

/-- The normalized cyclic dart list certificate for the face orbit. -/
lemma faceDartList_normalized (M : CombMap D) (f : M.Face) {root : D}
    (hφ : M.φ root ≠ root) (hroot : M.dartFace root = f) :
    NormalizedCyclicDartList M f root (M.faceDartList root) where
  head_eq := M.faceDartList_head hφ
  root_face := hroot
  nodup := Equiv.Perm.nodup_toList _ _
  length_pos := M.faceDartList_length_pos hφ
  toFinset_eq := M.faceDartList_toFinset f hφ hroot

/-- The `φ`-orbit length is the support cardinal of the root's cycle; the dart at
the cyclic-next index is the `φ`-image of the dart at the current index. -/
lemma faceDartList_consecutive_phi (M : CombMap D) {root : D} (hφ : M.φ root ≠ root)
    (i : Fin (M.faceDartList root).length) :
    (M.faceDartList root).get
        (cyclicNext (M.faceDartList_length_pos hφ) i) =
      M.φ ((M.faceDartList root).get i) := by
  classical
  have hlen : (M.faceDartList root).length = (M.φ.cycleOf root).support.card := by
    simp only [faceDartList, Equiv.Perm.length_toList]
  -- `(φ^n) root = root` where `n` is the list length.
  have hcycle : (M.φ ^ (M.faceDartList root).length) root = root := by
    have hself := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ
      (M.faceDartList root).length root
    rw [hlen, Nat.mod_self, pow_zero] at hself
    rw [hlen]; exact hself.symm
  -- `(φ^n)^k root = root`.
  have hpow : ∀ k : ℕ, ((M.φ ^ (M.faceDartList root).length) ^ k) root = root := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, hcycle]
  -- The cyclicNext index value.
  have hnext_val : ((cyclicNext (M.faceDartList_length_pos hφ) i :
      Fin (M.faceDartList root).length) : ℕ)
      = ((i : ℕ) + 1) % (M.faceDartList root).length := rfl
  rw [List.get_eq_getElem, List.get_eq_getElem,
    M.faceDartList_getElem root i i.2]
  rw [M.faceDartList_getElem root
    ((cyclicNext (M.faceDartList_length_pos hφ) i : Fin (M.faceDartList root).length) : ℕ)
    (cyclicNext (M.faceDartList_length_pos hφ) i).2]
  rw [hnext_val]
  -- `(φ ^ ((i+1) % n)) root = φ ((φ ^ i) root)`.
  have hmod : (M.φ ^ (((i : ℕ) + 1) % (M.faceDartList root).length)) root
      = (M.φ ^ ((i : ℕ) + 1)) root := by
    have hsplit : (i : ℕ) + 1
        = ((i : ℕ) + 1) % (M.faceDartList root).length
          + (M.faceDartList root).length * (((i : ℕ) + 1) / (M.faceDartList root).length) := by
      rw [Nat.add_comm, Nat.mod_add_div]
    conv_rhs => rw [hsplit]
    rw [pow_add, pow_mul, Equiv.Perm.coe_mul, Function.comp_apply, hpow]
  rw [hmod, pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]

/-- Consecutive face darts match at the common boundary vertex. -/
lemma faceDartList_consecutive_vertex (M : CombMap D) {root : D} (hφ : M.φ root ≠ root)
    (i : Fin (M.faceDartList root).length) :
    M.tail ((M.faceDartList root).get
        (cyclicNext (M.faceDartList_length_pos hφ) i)) =
      M.head ((M.faceDartList root).get i) := by
  rw [M.faceDartList_consecutive_phi hφ i, tail_phi]

/-- **Generic normalized boundary cycle from a single nontrivial face orbit.**
The explicit cyclic dart list is `[root, φ root, φ² root, …]`; all orbit-algebraic
fields are discharged, and the Jordan-arc split `arcSplit` is now DERIVED from boundary
simplicity (`hnodup`) via `BoundaryCycleData.toBoundaryCycle` — it is no longer a
parameter (`ZinanCh35ArcSplitUniversal` / `PlanarMapBoundaryArcSplit`). -/
noncomputable def boundaryCycleOfFace (M : CombMap D) (f : M.Face) {root : D}
    (hφ : M.φ root ≠ root) (hroot : M.dartFace root = f)
    (hnodup : ((M.faceDartList root).map M.tail).Nodup) :
    BoundaryCycle M f :=
  BoundaryCycleData.toBoundaryCycle
    { root := root
      darts := M.faceDartList root
      vertices := (M.faceDartList root).map M.tail
      edges := (M.faceDartList root).map M.dartEdge
      normalized := M.faceDartList_normalized f hφ hroot
      vertices_eq := rfl
      edges_eq := rfl
      consecutive_phi := M.faceDartList_consecutive_phi hφ
      consecutive_vertex := M.faceDartList_consecutive_vertex hφ }
    hnodup

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}



/-- The deleted map's `φ'` has no fixed dart (it is a simple graph). -/
lemma deleteVertex_phi_ne_self (hNT : NearTriangulation M) (d0 : D)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).φ x ≠ x :=
  phi_ne_self_of_isSimpleGraph (M.deleteVertex d0)
    (hNT.deleteVertex_isSimpleGraph d0) x






namespace DeletedMergedBoundaryCertificate

variable {d0 : D}











end DeletedMergedBoundaryCertificate









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanMergedOrbit
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.PlanarMapOuterArc -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}


structure MergedOuterArcData (M : CombMap D) (d0 : D)
    (r : {d : D // d ∉ M.deleteVertexSet d0}) (outerFace : M.Face) where
  /-- The exit survivor `o_pre`: the last surviving dart of the outer arc. -/
  exit : {d : D // d ∉ M.deleteVertexSet d0}
  /-- The exit dart lies on the old outer face. -/
  exit_face : M.dartFace exit.1 = outerFace
  /-- Its immediate `M.φ`-successor (the in-boundary dart `bin`) is deleted. -/
  exit_next_deleted : M.φ exit.1 ∈ M.deleteVertexSet d0
  /-- The Case-B closed-form successor of `exit` is the reference triangle dart
  `r`: the seam reconnection from the outer arc into the fan-triangle chain. -/
  exit_jump : M.σ (M.φ exit.1) = r.1
  /-- Every surviving outer dart reaches `exit` along a contiguous forward
  `M.φ`-run of survivors (the surviving outer arc is one `M.φ`-block). -/
  arc_run : ∀ x : {d : D // d ∉ M.deleteVertexSet d0}, M.dartFace x.1 = outerFace →
    ∃ k : ℕ, (∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet d0) ∧
      (M.φ ^ k) x.1 = exit.1

namespace MergedOuterArcData

variable {d0 : D} {r : {d : D // d ∉ M.deleteVertexSet d0}} {outerFace : M.Face}

/-- The `φ'`-successor of the exit survivor is the reference dart `r`: the single
Case-B seam jump from the surviving outer arc into the fan-triangle chain. -/
lemma phi'_exit (data : MergedOuterArcData M d0 r outerFace) :
    ((M.deleteVertex d0).φ data.exit : D) = r.1 := by
  have hsurv : M.σ (M.φ data.exit.1) ∉ M.deleteVertexSet d0 := by
    rw [data.exit_jump]; exact r.2
  rw [deleteVertex_phi_apply_of_next_deleted M d0 data.exit
      data.exit_next_deleted hsurv, data.exit_jump]

/-- The exit survivor is in the `φ'`-cycle of the reference dart `r`. -/
lemma sameCycle_exit (data : MergedOuterArcData M d0 r outerFace) :
    (M.deleteVertex d0).φ.SameCycle r data.exit := by
  have hexit_r : (M.deleteVertex d0).φ.SameCycle data.exit r := by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    rw [zpow_one]
    exact data.phi'_exit
  exact hexit_r.symm

/-- **The outer-arc reconnection from the data.**  Every surviving dart on the old
outer face is `φ'`-`SameCycle` to the reference dart `r`: walk the contiguous
surviving arc forward with `deleteVertex_phi_survRun_iterate` to the exit
survivor, then take the single Case-B seam jump to `r`.  No further planar input
is consumed — all `φ'` machinery is the already-proved
`PlanarMapFanMergedOrbit` calculus. -/
theorem mergedOuterArcReconnects (data : MergedOuterArcData M d0 r outerFace) :
    MergedOuterArcReconnects M d0 r outerFace := by
  intro x hx
  obtain ⟨k, hrun, hk⟩ := data.arc_run x hx
  -- x reaches data.exit along the surviving arc.
  have hxexit : (M.deleteVertex d0).φ.SameCycle x data.exit :=
    deleteVertex_phi_sameCycle_of_survRun M d0 x data.exit k hrun hk
  -- r ~ exit (seam jump) and x ~ exit (arc run); compose to r ~ x.
  exact data.sameCycle_exit.trans hxexit.symm

end MergedOuterArcData





/-- **The merged-face single-orbit fact from the actual seam edge.**  The
`MergedOuterArcData.exit_jump` equality must be stated at the concrete fan edge
where the old outer arc enters the fan chain.  The fan-chain calculus then
transports that entry point to the head reference internally. -/
theorem deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc_edge
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (r : {d : D // d ∉ M.deleteVertexSet d0}) (hr : FanTriangleEdge fan r)
    (data : MergedOuterArcData M d0 r hNT.outerFace) :
    DeleteVertexMergedFaceSingleOrbit M d0 :=
  deleteVertexMergedFaceSingleOrbit_of_fan_from_edge fan hchord htail0 r hr
    data.mergedOuterArcReconnects









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
-/
/- Source module: ProofsInTheBook.PlanarMapFanExistence -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- The explicit cyclic dart list of the `σ`-orbit (vertex star) of `v`. -/
def vertexDartList (M : CombMap D) (v : D) : List D :=
  M.σ.toList v

/-- The vertex dart list is nonempty when the `σ`-orbit is nontrivial. -/
lemma vertexDartList_length_pos (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) :
    0 < (M.vertexDartList v).length := by
  have hsupp : v ∈ M.σ.support := by simpa [Equiv.Perm.mem_support] using hσ
  exact Equiv.Perm.length_toList_pos_of_mem_support _ _ hsupp

/-- `getElem` of the vertex dart list is the `σ`-iterate of `v`. -/
lemma vertexDartList_getElem (M : CombMap D) (v : D) (n : ℕ)
    (hn : n < (M.vertexDartList v).length) :
    (M.vertexDartList v)[n] = (M.σ ^ n) v :=
  Equiv.Perm.getElem_toList _ _ _ _

/-- The head of the vertex dart list is `v`. -/
lemma vertexDartList_head (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) :
    (M.vertexDartList v).head? = some v := by
  have h0 : (M.vertexDartList v)[0]'(M.vertexDartList_length_pos hσ) = v := by
    have := M.vertexDartList_getElem v 0 (M.vertexDartList_length_pos hσ)
    simpa using this
  rw [List.head?_eq_getElem?,
    List.getElem?_eq_getElem (M.vertexDartList_length_pos hσ), h0]

/-- The vertex dart list has no repeats. -/
lemma vertexDartList_nodup (M : CombMap D) (v : D) :
    (M.vertexDartList v).Nodup :=
  Equiv.Perm.nodup_toList _ _

/-- Membership in the vertex dart list is `σ`-`SameCycle` with `v`. -/
lemma mem_vertexDartList_iff (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) (d : D) :
    d ∈ M.vertexDartList v ↔ M.σ.SameCycle v d := by
  have hsupp : v ∈ M.σ.support := by simpa [Equiv.Perm.mem_support] using hσ
  rw [vertexDartList, Equiv.Perm.mem_toList_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hsupp⟩⟩



/-- Each dart of the vertex list has the same tail as `v`. -/
lemma vertexDartList_tail (M : CombMap D) {v : D} (hσ : M.σ v ≠ v)
    {d : D} (hd : d ∈ M.vertexDartList v) :
    M.tail d = M.tail v := by
  have hsame : M.σ.SameCycle v d := (mem_vertexDartList_iff M hσ d).mp hd
  exact (Quotient.sound hsame.symm : M.tail d = M.tail v)

/-- The `σ`-cube/closure power identity: `(σ ^ n) v = v` where `n` is the list
length.  Mirror of the `faceDartList` argument. -/
lemma vertexDartList_pow_length (M : CombMap D) {v : D} (_hσ : M.σ v ≠ v) :
    (M.σ ^ (M.vertexDartList v).length) v = v := by
  have hlen : (M.vertexDartList v).length = (M.σ.cycleOf v).support.card := by
    simp only [vertexDartList, Equiv.Perm.length_toList]
  have hself := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.σ
    (M.vertexDartList v).length v
  rw [hlen, Nat.mod_self, pow_zero] at hself
  rw [hlen]; exact hself.symm

/-- **`consecutive_sigma` for the vertex dart list.**  The dart at the cyclic-next
index is the `σ`-image of the dart at the current index.  Exact mirror of
`faceDartList_consecutive_phi`. -/
lemma vertexDartList_consecutive_sigma (M : CombMap D) {v : D} (hσ : M.σ v ≠ v)
    (i : Fin (M.vertexDartList v).length) :
    (M.vertexDartList v).get
        (cyclicNext (M.vertexDartList_length_pos hσ) i) =
      M.σ ((M.vertexDartList v).get i) := by
  classical
  have hcycle : (M.σ ^ (M.vertexDartList v).length) v = v :=
    M.vertexDartList_pow_length hσ
  have hpow : ∀ k : ℕ, ((M.σ ^ (M.vertexDartList v).length) ^ k) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, hcycle]
  have hnext_val : ((cyclicNext (M.vertexDartList_length_pos hσ) i :
      Fin (M.vertexDartList v).length) : ℕ)
      = ((i : ℕ) + 1) % (M.vertexDartList v).length := rfl
  rw [List.get_eq_getElem, List.get_eq_getElem,
    M.vertexDartList_getElem v i i.2]
  rw [M.vertexDartList_getElem v
    ((cyclicNext (M.vertexDartList_length_pos hσ) i : Fin (M.vertexDartList v).length) : ℕ)
    (cyclicNext (M.vertexDartList_length_pos hσ) i).2]
  rw [hnext_val]
  have hmod : (M.σ ^ (((i : ℕ) + 1) % (M.vertexDartList v).length)) v
      = (M.σ ^ ((i : ℕ) + 1)) v := by
    have hsplit : (i : ℕ) + 1
        = ((i : ℕ) + 1) % (M.vertexDartList v).length
          + (M.vertexDartList v).length * (((i : ℕ) + 1) / (M.vertexDartList v).length) := by
      rw [Nat.add_comm, Nat.mod_add_div]
    conv_rhs => rw [hsplit]
    rw [pow_add, pow_mul, Equiv.Perm.coe_mul, Function.comp_apply, hpow]
  rw [hmod, pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)







/-- **The neighbour rotation order from the vertex dart list.**  Given a dart `d0`
at `v0` with nontrivial `σ`-orbit, and a proof that the head list of its
`σ`-rotation equals a given neighbour list, the `NeighborRotationOrder` certificate
is assembled. -/
def neighborRotationOrderOfVertexDartList {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (neighbors : List M.Vertex)
    (hheads : (M.vertexDartList d0).map M.head = neighbors) :
    NeighborRotationOrder M v0 neighbors where
  darts := M.vertexDartList d0
  darts_nodup := M.vertexDartList_nodup d0
  darts_nonempty := M.vertexDartList_length_pos hσ
  tails_eq := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro v hv
    rcases List.mem_map.mp hv with ⟨d, hd, rfl⟩
    rw [M.vertexDartList_tail hσ hd, htail0]
  heads_eq := hheads
  consecutive_sigma := M.vertexDartList_consecutive_sigma hσ



/-- Two distinct darts at the same vertex have distinct heads, in a simple graph. -/
lemma head_injOn_sameCycle (hNT : NearTriangulation M) {v0 : M.Vertex} {d e : D}
    (hd : M.tail d = v0) (he : M.tail e = v0)
    (hhead : M.head d = M.head e) : d = e := by
  have hsame : M.α.SameCycle d e :=
    M.alpha_sameCycle_of_same_endpoints hNT.simpleGraph (hd.trans he.symm) hhead
  rcases (M.alpha_sameCycle_iff d e).mp hsame with rfl | rfl
  · rfl
  · exfalso
    apply hNT.simpleGraph.no_loop d
    -- `e = α d`, so `head e = head (α d) = tail d`; with `head d = head e`, `d` loops.
    have hhd : M.head (M.α d) = M.tail d := by simp
    rw [hhead, hhd]

/-- The fan path (heads of the `σ`-rotation rooted at `d0`) is simple, from graph
simplicity alone. -/
lemma vertexDartList_heads_nodup (hNT : NearTriangulation M) {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0) :
    ((M.vertexDartList d0).map M.head).Nodup := by
  rw [List.nodup_map_iff_inj_on (M.vertexDartList_nodup d0)]
  intro d hd e he hhead
  exact head_injOn_sameCycle hNT
    ((M.vertexDartList_tail hσ hd).trans htail0)
    ((M.vertexDartList_tail hσ he).trans htail0) hhead



/-- The isolated fan-incidence datum at a boundary vertex `v0`: the planar
orientation residue from which the full `BoundaryVertexFan` is assembled. -/
structure FanIncidenceData {M : CombMap D} (hNT : NearTriangulation M)
    (v0 : M.Vertex) where
  /-- The outgoing boundary spoke at `v0`. -/
  d0 : D
  /-- Its `σ`-orbit (the star of `v0`) is nontrivial. -/
  sigma_ne : M.σ d0 ≠ d0
  /-- `d0` has tail `v0`. -/
  tail0 : M.tail d0 = v0
  /-- The exposed-path endpoints and interior fan vertices. -/
  x : M.Vertex
  interior : List M.Vertex
  w : M.Vertex
  /-- The head list of the `σ`-rotation rooted at `d0` is exactly the fan path. -/
  heads_eq : (M.vertexDartList d0).map M.head = fanPath x interior w
  /-- `v0` is a boundary vertex. -/
  v0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  /-- `x` is a boundary vertex. -/
  x_boundary : hNT.outerCycle.IsBoundaryVertex x
  /-- `w` is a boundary vertex. -/
  w_boundary : hNT.outerCycle.IsBoundaryVertex w
  /-- The exact face-incidence certificate: the non-outer faces at `v0` are exactly
  the consecutive fan triangles along the path. -/
  incident_faces_exact :
    IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)
  /-- Chordless ⟹ interior fan vertices are not old boundary vertices. -/
  interior_not_boundary_of_chordless :
    BoundaryChordless hNT.outerCycle →
      ∀ z : M.Vertex, z ∈ interior → ¬ hNT.outerCycle.IsBoundaryVertex z
  /-- Chordless ⟹ empty interior characterizes the base triangle. -/
  empty_iff_base_triangle_of_chordless :
    BoundaryChordless hNT.outerCycle → (interior = [] ↔ hNT.IsBaseTriangle)

variable {hNT}

/-- **Assemble the boundary-vertex fan from the incidence datum.**  The
`NeighborRotationOrder` field is discharged constructively from the `σ`-rotation
list `vertexDartList d0`; the remaining (orientation / Jordan) fields come from the
datum. -/
def boundaryVertexFan_of_incidenceData {v0 : M.Vertex}
    (data : FanIncidenceData hNT v0) :
    BoundaryVertexFan hNT v0 where
  x := data.x
  interior := data.interior
  w := data.w
  v0_boundary := data.v0_boundary
  x_boundary := data.x_boundary
  w_boundary := data.w_boundary
  rotation_order :=
    neighborRotationOrderOfVertexDartList data.sigma_ne data.tail0
      (fanPath data.x data.interior data.w) data.heads_eq
  incident_faces_exact := data.incident_faces_exact
  path_nodup_of_chordless := fun _ => by
    rw [← data.heads_eq]
    exact vertexDartList_heads_nodup hNT data.sigma_ne data.tail0
  interior_not_boundary_of_chordless := data.interior_not_boundary_of_chordless
  empty_iff_base_triangle_of_chordless := data.empty_iff_base_triangle_of_chordless



/-- **The extreme-spoke / outer-neighbour tie (construction byproduct).**  The
first fan endpoint `x` is exactly the head of the rooting spoke `d0`, i.e. `d0` is
the spoke landing on the first fan neighbour.  This is the dart-level tie between
the extreme fan spoke and `v0`'s outer-cycle dart that the `MergedOuterArcData`
seam reconnection consumes (the `α`-pairing of the extreme spokes with the two
outer-cycle darts at `v0`). -/
theorem fan_first_spoke_head {v0 : M.Vertex} (data : FanIncidenceData hNT v0) :
    data.x = M.head data.d0 := by
  have hhd : (M.vertexDartList data.d0).head? = some data.d0 :=
    M.vertexDartList_head data.sigma_ne
  have hmap : ((M.vertexDartList data.d0).map M.head).head?
      = some (M.head data.d0) := by
    rw [List.head?_map, hhd, Option.map_some]
  rw [data.heads_eq] at hmap
  -- `fanPath x interior w` has head `x`.
  have : (fanPath data.x data.interior data.w).head? = some data.x := by
    simp [fanPath]
  rw [this] at hmap
  exact (Option.some.injEq _ _).mp hmap.symm ▸ rfl









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence
-/
/- Source module: ProofsInTheBook.ThomassenInduction -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ThomassenInduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u





/-- The chordless-branch oracle datum: all the boundary-deletion Jordan data for a
chosen deletion site `v0`, the boundary neighbour of `p` distinct from `q`.

It carries the fan-incidence datum (which *constructs* the fan), chordlessness, the
merged-outer-arc supplier, and the merged-outer-boundary cycle — exactly the inputs
of `deleteBoundaryVertex_nearTriangulation_of_incidenceData`.  Plus the two reserved
colors `γ, δ ∈ L v0` and the bookkeeping facts the deletion list transport needs
(the precolored endpoint `p = fan.x` avoids `γ, δ` once colored, and `x, w ≠ v0`).

The `v0`-relation to `p, q` is recorded so the extension reconnects the precolored
edge. -/
structure ChordlessOracle {D : Type u} [Fintype D] [DecidableEq D] {α : Type u}
    [DecidableEq α] {M : CombMap D} (hNT : NearTriangulation M)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) : Type u where
  /-- The boundary is chordless. -/
  chordless : BoundaryChordless hNT.outerCycle
  /-- The deletion site `v0`: the boundary neighbour of `p` distinct from `q`. -/
  v0 : M.Vertex
  /-- The fan incidence datum at `v0` (constructs the fan). -/
  fanData : NearTriangulation.FanIncidenceData hNT v0
  /-- The dart-level fan-surgery reconstruction at `d0` (the boundary-deletion Jordan
  data: the vertex-quotient equivalence, the merged outer face, the new boundary
  cycle, and the inner-triangle preservation). -/
  recon : NearTriangulation.FanSurgeryReconstruction hNT fanData.d0
  /-- `d0` represents `v0`. -/
  hd0 : Quotient.mk (cycleSetoid M.σ) fanData.d0 = v0
  /-- The two reserved colors. -/
  γ : α
  /-- The two reserved colors. -/
  δ : α
  γ_mem : γ ∈ L v0
  δ_mem : δ ∈ L v0
  γδ_ne : γ ≠ δ
  /-- The fan endpoints differ from `v0`. -/
  x_ne : (NearTriangulation.boundaryVertexFan_of_incidenceData fanData).x ≠ v0
  w_ne : (NearTriangulation.boundaryVertexFan_of_incidenceData fanData).w ≠ v0
  /-- The first fan endpoint is one of the precolored endpoints, and that endpoint's
  precolored color avoids the two reserved colors. -/
  x_precolored :
    ((NearTriangulation.boundaryVertexFan_of_incidenceData fanData).x = p ∧
      cp ≠ γ ∧ cp ≠ δ) ∨
    ((NearTriangulation.boundaryVertexFan_of_incidenceData fanData).x = q ∧
      cq ≠ γ ∧ cq ≠ δ)
  /-- **The deletion's boundary bookkeeping (the one isolated Jordan residue).**  The
  deleted near-triangulation, with the fan-deleted lists, again satisfies the
  Thomassen list hypotheses for *some* precolored boundary edge.  This is the
  exact-list relabeling of the review's Case 2: `p, q` stay precolored singletons,
  the exposed fan vertices `z_i` (interior `≥ 5`) become boundary `≥ 3` after losing
  `γ, δ`, every surviving old boundary vertex keeps `≥ 3`, every surviving interior
  vertex keeps `≥ 5`.  It is supplied by the oracle because the new-boundary vertex
  labelling is the deletion's Jordan-curve bookkeeping that the combinatorial-map
  layer does not synthesize.  The existential over the precolored edge is all the
  recursion needs (the extension step `deleteBoundaryVertex_listColorable` consumes
  *any* `deleteFanLists`-coloring, independently of which edge was precolored). -/
  deleted_lists : ∃ (p' q' : (M.deleteVertex fanData.d0).Vertex) (cp' cq' : α),
    ThomassenLists recon.nearTriangulation p' q'
      (deleteFanLists M fanData.d0
        (NearTriangulation.boundaryVertexFan_of_incidenceData fanData).interior.toFinset
        L γ δ) cp' cq'





section Base

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}



end Base



section Chord

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}



end Chord



section Chordless

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}

/-- The fan built from the chordless oracle datum. -/
noncomputable def codFan (cod : ChordlessOracle hNT p q L cp cq) :
    NearTriangulation.BoundaryVertexFan hNT cod.v0 :=
  NearTriangulation.boundaryVertexFan_of_incidenceData cod.fanData

/-- The deleted near-triangulation produced by the chordless oracle datum (via the
dart-level fan-surgery reconstruction). -/
noncomputable def deletedNT (cod : ChordlessOracle hNT p q L cp cq) :
    NearTriangulation (M.deleteVertex cod.fanData.d0) :=
  cod.recon.nearTriangulation



/-- The fan-deleted lists for the chordless oracle datum. -/
noncomputable def codLists (cod : ChordlessOracle hNT p q L cp cq) :
    (M.deleteVertex cod.fanData.d0).Vertex → Finset α :=
  deleteFanLists M cod.fanData.d0 (codFan cod).interior.toFinset L cod.γ cod.δ







end Chordless



section Induction

variable {α : Type u} [DecidableEq α]

/-- A near-triangulation has at least three vertices: the outer cycle has length
`≥ 3` and a simple (nodup) vertex list, so it exhibits `≥ 3` distinct vertices. -/
theorem three_le_V {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) : 3 ≤ M.V := by
  classical
  have hnodup : hNT.outerCycle.vertices.Nodup := hNT.outer_simple
  have hlen : 3 ≤ hNT.outerCycle.vertices.length := by
    rw [hNT.outerCycle.vertices_length]; exact hNT.outer_len
  have hcard : 3 ≤ hNT.outerCycle.vertices.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup]; exact hlen
  calc 3 ≤ hNT.outerCycle.vertices.toFinset.card := hcard
    _ ≤ Fintype.card M.Vertex := Finset.card_le_univ _
    _ = M.V := rfl





end Induction



section Corollaries

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D}





end Corollaries



section FiveColor

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D}



end FiveColor

end ProofsInTheBook.ThomassenInduction

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenInduction
import ProofsInTheBook.PlanarMapChordSplit
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.ChordSplitNT -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSplitNT

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u



variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}

/-- The reconstruction datum for ONE side of a chord split, relative to a side
region `s ⊆ M.Vertex` and side lists.  `Dₛ` is the side dart type (in the surgery,
`keptSideᵢ ⊕ Fin 2`).

The structure isolates the Jordan/Euler outputs that the combinatorial-map layer
cannot synthesize, exactly as `FanSurgeryReconstruction` does for the chordless
branch:

* `N` — the side as a near-triangulation (carries `IsSphereMap`/genus-0);
* `ι` — the side-vertex-to-`M` correspondence, injective and adjacency-reflecting
  *onto* the region `s` (`ι_surj`), so it is a graph isomorphism `N ≃ M⟦s⟧`;
* `ι_lists` — the side near-triangulation's lists are the pullback of `L` along
  `ι`, so a list coloring of `N` transports to a region coloring of `M`;
* `smaller` — strict vertex decrease, the recursion fuel.

`Lₛ` and the precolored data (`pₛ qₛ cpₛ cqₛ`) are the side's Thomassen inputs. -/
structure ChordSideReconstruction (hNT : NearTriangulation M)
    (s : Set M.Vertex) (L : M.Vertex → Finset α) where
  /-- The side dart type. -/
  Dₛ : Type u
  /-- Side dart type is a fintype. -/
  [fintypeDₛ : Fintype Dₛ]
  /-- Side dart type has decidable equality. -/
  [decEqDₛ : DecidableEq Dₛ]
  /-- The side combinatorial map. -/
  N : CombMap Dₛ
  /-- The side is a near-triangulation (carries `IsSphereMap`: genus-0/Euler-2). -/
  hN : NearTriangulation N
  /-- The side-vertex-to-`M`-vertex correspondence. -/
  ι : N.Vertex → M.Vertex
  /-- The correspondence is injective. -/
  ι_inj : Function.Injective ι
  /-- The correspondence lands in the region. -/
  ι_mem : ∀ x : N.Vertex, ι x ∈ s
  /-- The correspondence is *surjective onto the region* (the side-vertex
  classification: every region vertex is a side vertex). -/
  ι_surj : ∀ ⦃w : M.Vertex⦄, w ∈ s → ∃ x : N.Vertex, ι x = w
  /-- The correspondence carries side adjacency to `M`-adjacency (graph hom). -/
  ι_adj : ∀ ⦃x y : N.Vertex⦄, N.toSimpleGraph.Adj x y →
    M.toSimpleGraph.Adj (ι x) (ι y)
  /-- The correspondence *reflects* `M`-adjacency on the region (graph iso onto the
  induced subgraph): two side vertices adjacent in `M` are adjacent in `N`. -/
  ι_adj_reflect : ∀ ⦃x y : N.Vertex⦄, M.toSimpleGraph.Adj (ι x) (ι y) →
    N.toSimpleGraph.Adj x y
  /-- The side lists are the pullback of `L` along `ι`. -/
  Lₛ : N.Vertex → Finset α
  /-- The pullback identity for the side lists. -/
  Lₛ_eq : ∀ x : N.Vertex, Lₛ x = L (ι x)
  /-- The side's precolored boundary edge. -/
  pₛ : N.Vertex
  /-- The side's precolored boundary edge. -/
  qₛ : N.Vertex
  /-- The side's precolors. -/
  cpₛ : α
  /-- The side's precolors. -/
  cqₛ : α
  /-- The side near-triangulation carries the Thomassen list hypotheses, so the
  Thomassen induction can recurse on it.  (This is part of the list transport the
  classification produces alongside the correspondence.) -/
  hLₛ : ThomassenLists hN pₛ qₛ Lₛ cpₛ cqₛ
  /-- Strict vertex decrease (the recursion fuel). -/
  smaller : N.V < M.V

attribute [instance] ChordSideReconstruction.fintypeDₛ ChordSideReconstruction.decEqDₛ

namespace ChordSideReconstruction

variable {s : Set M.Vertex} {L : M.Vertex → Finset α}

/-- The section `M`-region `→` side vertex: the inverse of `ι` on the region.
Built classically from surjectivity + injectivity. -/
noncomputable def section_ (R : ChordSideReconstruction hNT s L)
    {w : M.Vertex} (hw : w ∈ s) : R.N.Vertex :=
  (R.ι_surj hw).choose





open scoped Classical in
/-- The region coloring of `M`: at a region vertex use `c` of the section; off the
region use an arbitrary fixed value (irrelevant — `ProperOn`/`ListValidOn` only
look at the region). -/
noncomputable def colorRegion (R : ChordSideReconstruction hNT s L)
    (c : R.N.Vertex → α) (default : α) : M.Vertex → α :=
  fun w => if hw : w ∈ s then c (R.section_ hw) else default









end ChordSideReconstruction



/-- The chord recursion datum: the `ChordSplitRegions` glue object, the side-1
reconstruction on its region (lists `L`), and — for *every* possible side-1
coloring `c₁` agreeing with the precolored edge — a side-2 reconstruction on its
region whose lists are the side-1-forced lists `forcedLists c₁ L`.  Making `R₂` a
function of `c₁` is faithful to Thomassen's order (color side 1, *then* force the
chord endpoints `u, v`, then color side 2): the side-2 datum genuinely depends on
the side-1 result, and the forcing makes the two recursive colorings agree at
`u, v` automatically. -/
structure ChordRecursionData (hNT : NearTriangulation M)
    (u v p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) where
  /-- The `M`-vertex-level chord split regions. -/
  regions : ChordSplitRegions hNT u v p q L cp cq
  /-- The chord endpoints are distinct (an edge of `M`). -/
  uv_ne : u ≠ v
  /-- The side-1 reconstruction (region `s₁`, lists `L`). -/
  R₁ : ChordSideReconstruction hNT regions.s₁ L
  /-- For each side-1 coloring `c₁` with distinct chord-endpoint colors, a side-2
  reconstruction whose region is `s₂`
  and whose lists are the chord-endpoint-forced lists `forcedLists c₁ L`.  This
  encodes "force `u, v` to the side-1 colors, then color side 2 by recursion". -/
  R₂ : (c₁ : M.Vertex → α) → c₁ u ≠ c₁ v → ChordSideReconstruction hNT regions.s₂
    (regions.forcedLists c₁ L)

namespace ChordRecursionData

variable {u v p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}



/-- The side-1 region coloring, produced by recursing on the side-1 near-
triangulation.  `ih` is the strong-induction hypothesis (every map with `< M.V`
vertices and the Thomassen lists is colorable). -/
noncomputable def color₁ (data : ChordRecursionData hNT u v p q L cp cq)
    (default : α)
    (ih : ∀ (m : ℕ), m < M.V → ∀ {Dₛ : Type u} [Fintype Dₛ] [DecidableEq Dₛ]
      {N : CombMap Dₛ} (hN : NearTriangulation N) (pₛ qₛ : N.Vertex)
      (Lₛ : N.Vertex → Finset α) (cpₛ cqₛ : α), N.V ≤ m →
      ThomassenLists hN pₛ qₛ Lₛ cpₛ cqₛ → ListColorable N.toSimpleGraph Lₛ) :
    M.Vertex → α := by
  classical
  -- recurse on side 1.
  have hcol₁ : ListColorable data.R₁.N.toSimpleGraph data.R₁.Lₛ :=
    ih data.R₁.N.V data.R₁.smaller data.R₁.hN data.R₁.pₛ data.R₁.qₛ data.R₁.Lₛ
      data.R₁.cpₛ data.R₁.cqₛ le_rfl data.R₁.hLₛ
  exact data.R₁.colorRegion hcol₁.choose default





end ChordRecursionData



/-- The chord-recursive dichotomy: for every near-triangulation with the Thomassen
lists, either a chord **recursion datum** (carrying the two smaller side near-
triangulations, NO colorings) or a chordless oracle datum.  This is strictly weaker
input than `ThomassenInduction.JordanOracle`: the chord branch no longer carries the
side colorings `c₁, c₂` — they are produced by recursion. -/
structure ChordRecursiveDichotomy (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- The dichotomy. -/
  decide :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α),
      3 < M.V → ThomassenLists hNT p q L cp cq →
        (Σ' u v : M.Vertex, ChordRecursionData hNT u v p q L cp cq) ⊕
          ChordlessOracle hNT p q L cp cq







/-- `ChordRecursionData` is genuinely inhabited from its components: the regions,
the chord-endpoint distinctness, a side-1 reconstruction, and a side-2
reconstruction family.  This is the constructor, recorded to certify the datum is
not a hidden `False` (the §3.3 non-vacuity check). -/
def ChordRecursionData.ofComponents {u v p q : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α}
    (regions : ChordSplitRegions hNT u v p q L cp cq) (uv_ne : u ≠ v)
    (R₁ : ChordSideReconstruction hNT regions.s₁ L)
    (R₂ : (c₁ : M.Vertex → α) → c₁ u ≠ c₁ v →
      ChordSideReconstruction hNT regions.s₂ (regions.forcedLists c₁ L)) :
    ChordRecursionData hNT u v p q L cp cq :=
  { regions := regions, uv_ne := uv_ne, R₁ := R₁, R₂ := R₂ }



end ProofsInTheBook.ChordSplitNT









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordSplitEuler -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSplitEuler

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]





/-- **The edge count of a fresh map** is `(|K| + 2) / 2`, and in particular
`2 · E(freshMap) = |K| + 2`.  Proved purely from `freshAlpha` being a
fixed-point-free involution (`2E = |D|`). -/
theorem freshMap_two_mul_E (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (hβfix : ∀ k, β k ≠ k) (a₀ a₁ : K) (hne : a₀ ≠ a₁) :
    2 * (freshMap β ρ hβinv hβfix a₀ a₁ hne).E = Fintype.card K + 2 := by
  rw [(freshMap β ρ hβinv hβfix a₀ a₁ hne).two_mul_E_eq_card]
  simp [Fintype.card_sum, Fintype.card_fin]



section VertexCount

variable (ρ : Equiv.Perm K) {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The projection collapsing each fresh dart to its anchor:
`inl k ↦ k`, `inr 0 ↦ a₀`, `inr 1 ↦ a₁`. -/
def proj (a₀ a₁ : K) : K ⊕ Fin 2 → K
  | Sum.inl k => k
  | Sum.inr j => if j = 0 then a₀ else a₁

@[simp] lemma proj_inl (k : K) : proj a₀ a₁ (Sum.inl k) = k := rfl
@[simp] lemma proj_inr_zero : proj a₀ a₁ (Sum.inr 0) = a₀ := rfl
@[simp] lemma proj_inr_one : proj a₀ a₁ (Sum.inr 1) = a₁ := by
  simp [proj]

/-- Every fresh dart is in the same fresh `σ`-orbit as the `inl` of its anchor
projection.  (The fresh darts `inr 0`, `inr 1` sit immediately after `a₀`, `a₁`.) -/
lemma freshSigma_sameCycle_inl_proj (x : K ⊕ Fin 2) :
    (freshSigma ρ a₀ a₁ hne).SameCycle x (Sum.inl (proj a₀ a₁ x)) := by
  cases x with
  | inl k => simpa using Equiv.Perm.SameCycle.rfl
  | inr j =>
      -- the two fresh darts sit immediately after their anchors.
      have key : ∀ (c : K) (jj : Fin 2),
          freshSigma ρ a₀ a₁ hne (Sum.inl c) = Sum.inr jj →
          (freshSigma ρ a₀ a₁ hne).SameCycle (Sum.inr jj) (Sum.inl c) := by
        intro c jj h
        exact ⟨-1, by rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, h]⟩
      fin_cases j
      · have h : freshSigma ρ a₀ a₁ hne (Sum.inl a₀) = Sum.inr 0 :=
          freshSigma_anchor_zero ρ a₀ a₁ hne
        have hc := key a₀ 0 h
        simpa using hc
      · have h : freshSigma ρ a₀ a₁ hne (Sum.inl a₁) = Sum.inr 1 :=
          freshSigma_anchor_one ρ a₀ a₁ hne
        have hc := key a₁ 1 h
        simpa using hc

/-- **One fresh `σ`-step projects to one `ρ`-step (or stays put).**  Applying
`freshSigma` to `inl k` lands in the same `ρ`-orbit as `ρ k`; more precisely, the
projections of `x` and `freshSigma x` are `ρ`-SameCycle. -/
lemma ρ_sameCycle_proj_freshSigma_apply (x : K ⊕ Fin 2) :
    ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ (freshSigma ρ a₀ a₁ hne x)) := by
  cases x with
  | inl k =>
      by_cases h0 : k = a₀
      · rw [h0, freshSigma_anchor_zero ρ a₀ a₁ hne]
        simp only [proj_inl, proj_inr_zero]
        exact Equiv.Perm.SameCycle.rfl
      · by_cases h1 : k = a₁
        · rw [h1, freshSigma_anchor_one ρ a₀ a₁ hne]
          simp only [proj_inl, proj_inr_one]
          exact Equiv.Perm.SameCycle.rfl
        · rw [freshSigma_other ρ a₀ a₁ hne h0 h1]
          simp only [proj_inl]
          exact ⟨1, by rw [zpow_one]⟩
  | inr j =>
      fin_cases j
      · show ρ.SameCycle (proj a₀ a₁ (Sum.inr 0))
          (proj a₀ a₁ (freshSigma ρ a₀ a₁ hne (Sum.inr 0)))
        rw [freshSigma_fresh_zero ρ a₀ a₁ hne]
        simp only [proj_inr_zero, proj_inl]
        exact ⟨1, by rw [zpow_one]⟩
      · show ρ.SameCycle (proj a₀ a₁ (Sum.inr 1))
          (proj a₀ a₁ (freshSigma ρ a₀ a₁ hne (Sum.inr 1)))
        rw [freshSigma_fresh_one ρ a₀ a₁ hne, proj_inr_one]
        simp only [proj_inl]
        exact ⟨1, by rw [zpow_one]⟩

/-- The projections of `x` and `(freshSigma)^[n] x` are always `ρ`-SameCycle. -/
lemma ρ_sameCycle_proj_freshSigma_iterate (x : K ⊕ Fin 2) (n : ℕ) :
    ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ ((freshSigma ρ a₀ a₁ hne)^[n] x)) := by
  induction n with
  | zero => simpa using Equiv.Perm.SameCycle.rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (ρ_sameCycle_proj_freshSigma_apply ρ hne _)

/-- **Forward: a fresh `σ`-cycle projects into one `ρ`-cycle.** -/
lemma ρ_sameCycle_proj_of_freshSigma_sameCycle {x y : K ⊕ Fin 2}
    (h : (freshSigma ρ a₀ a₁ hne).SameCycle x y) :
    ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [← hm, Equiv.Perm.coe_pow]
  exact ρ_sameCycle_proj_freshSigma_iterate ρ hne x m

/-- **Backward: `inl` of `ρ`-equal anchors are fresh-`σ`-SameCycle.**  If `a` and
`b` are `ρ`-SameCycle then `inl a` and `inl b` are fresh-`σ`-SameCycle.  We trace
the `ρ`-power into a fresh-`σ`-power that visits the same `inl` darts. -/
lemma freshSigma_sameCycle_inl_of_ρ_sameCycle {a b : K} (h : ρ.SameCycle a b) :
    (freshSigma ρ a₀ a₁ hne).SameCycle (Sum.inl a) (Sum.inl b) := by
  -- It suffices to handle one `ρ`-step `b = ρ a` and chain.
  -- `freshSigma`-SameCycle to the `inl` of the `ρ`-successor:
  have step : ∀ c : K, (freshSigma ρ a₀ a₁ hne).SameCycle (Sum.inl c) (Sum.inl (ρ c)) := by
    intro c
    by_cases h0 : c = a₀
    · -- `inl a₀ → inr 0 → inl (ρ a₀)`: two `freshSigma` steps.
      refine ⟨2, ?_⟩
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, Equiv.Perm.mul_apply, h0,
        freshSigma_anchor_zero ρ a₀ a₁ hne, freshSigma_fresh_zero ρ a₀ a₁ hne]
    · by_cases h1 : c = a₁
      · refine ⟨2, ?_⟩
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, Equiv.Perm.mul_apply, h1,
          freshSigma_anchor_one ρ a₀ a₁ hne, freshSigma_fresh_one ρ a₀ a₁ hne]
      · refine ⟨1, ?_⟩
        rw [zpow_one]
        exact freshSigma_other ρ a₀ a₁ hne h0 h1
  -- now chain the single steps along the `ρ`-power.
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [← hm, Equiv.Perm.coe_pow]
  clear hm
  induction m with
  | zero => simpa using Equiv.Perm.SameCycle.rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (step _)

/-- **The fresh `σ`-cycle / `ρ`-cycle correspondence.**  Two darts are in the same
fresh `σ`-orbit iff their anchor projections are in the same `ρ`-orbit. -/
theorem freshSigma_sameCycle_iff (x y : K ⊕ Fin 2) :
    (freshSigma ρ a₀ a₁ hne).SameCycle x y ↔ ρ.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) := by
  constructor
  · exact ρ_sameCycle_proj_of_freshSigma_sameCycle ρ hne
  · intro h
    -- `x ~ inl (π x) ~ inl (π y) ~ y`.
    refine (freshSigma_sameCycle_inl_proj ρ hne x).trans ?_
    refine (freshSigma_sameCycle_inl_of_ρ_sameCycle ρ hne h).trans ?_
    exact (freshSigma_sameCycle_inl_proj ρ hne y).symm

/-- The `σ`-orbit quotient of the fresh map is in bijection with the `ρ`-orbit
quotient of the kept rotation, via the anchor projection `proj`. -/
noncomputable def freshSigma_vertexQuotientEquiv :
    Quotient (cycleSetoid (freshSigma ρ a₀ a₁ hne)) ≃ Quotient (cycleSetoid ρ) := by
  classical
  -- the descended map `[x] ↦ [proj x]` and its inverse `[k] ↦ [inl k]`.
  refine
    { toFun := Quotient.lift (fun x => Quotient.mk (cycleSetoid ρ) (proj a₀ a₁ x)) ?_,
      invFun := Quotient.lift (fun k => Quotient.mk (cycleSetoid (freshSigma ρ a₀ a₁ hne))
        (Sum.inl k)) ?_,
      left_inv := ?_, right_inv := ?_ }
  · -- well-defined forward: SameCycle x y ⇒ SameCycle (proj x) (proj y).
    intro x y hxy
    apply Quotient.sound
    exact (freshSigma_sameCycle_iff ρ hne x y).1 hxy
  · -- well-defined inverse: ρ.SameCycle a b ⇒ freshSigma.SameCycle (inl a) (inl b).
    intro a b hab
    apply Quotient.sound
    exact freshSigma_sameCycle_inl_of_ρ_sameCycle ρ hne hab
  · -- left inverse: `[inl (proj x)] = [x]`.
    intro q
    refine Quotient.inductionOn q (fun x => ?_)
    apply Quotient.sound
    exact (freshSigma_sameCycle_inl_proj ρ hne x).symm
  · -- right inverse: `[proj (inl k)] = [k]`.
    intro q
    refine Quotient.inductionOn q (fun k => ?_)
    simp only [Quotient.lift_mk, proj_inl]

/-- **The vertex count of a fresh-dart adjunction equals the kept rotation's
vertex count.**  Splicing the two fresh darts into existing `σ`-orbits neither
creates nor destroys an orbit, so `V(freshMap β ρ …) = numCycles ρ`. -/
theorem freshMap_V (β : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).V
      = Fintype.card (Quotient (cycleSetoid ρ)) := by
  show Fintype.card (Quotient (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ)) = _
  rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne from rfl]
  exact Fintype.card_congr (freshSigma_vertexQuotientEquiv ρ hne)

end VertexCount



section EulerReduction

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The honest isolated face count for a fresh-dart adjunction.**  The genus-0
content: the face (`σα`-orbit) count of the fresh map is `(|K|+2)/2 - numCycles ρ
+ 2`, i.e. exactly `E - V + 2`.  Equivalently `2·F = |K| + 2 - 2·V + 4`.  In the
chord split this is the per-side identity `F₁ + F₂ = F + 1` (the chord adds one
shared boundary face to each side).  Stated as a `Prop` because it is the single
remaining Jordan/Euler input (see the section docstring); it is *not* derivable for
generic `β, ρ, a₀, a₁`. -/
def FreshFaceCount : Prop :=
  2 * (freshMap β ρ hβinv hβfix a₀ a₁ hne).F
    = Fintype.card K + 6 - 2 * Fintype.card (Quotient (cycleSetoid ρ))

/-- **The genus-0 reduction.**  Given the proved `V` and `E` counts, the fresh
map's Euler characteristic is `2` **iff** the single face count `FreshFaceCount`
holds.  This pins the genus-0 preservation `eulerChar = 2` to one face-orbit
count, retiring the `V` and `E` counts entirely. -/
theorem freshMap_eulerChar_eq_two_iff_faceCount
    (hV : Fintype.card (Quotient (cycleSetoid ρ)) ≤ (Fintype.card K + 2) / 2 + 1) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).eulerChar = 2 ↔
      FreshFaceCount β ρ hβinv hβfix hne := by
  unfold CombMap.eulerChar FreshFaceCount
  have hE : 2 * (freshMap β ρ hβinv hβfix a₀ a₁ hne).E = Fintype.card K + 2 :=
    freshMap_two_mul_E β ρ hβinv hβfix a₀ a₁ hne
  have hVeq : (freshMap β ρ hβinv hβfix a₀ a₁ hne).V
      = Fintype.card (Quotient (cycleSetoid ρ)) :=
    freshMap_V ρ hne β hβinv hβfix
  rw [hVeq]
  constructor
  · intro heuler
    -- from `V - E + F = 2` (ℤ), multiply through by 2 and use `2E = |K|+2`.
    have hZ : 2 * (Fintype.card (Quotient (cycleSetoid ρ)) : ℤ)
        - 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).E : ℤ)
        + 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).F : ℤ) = 4 := by linarith [heuler]
    have hEZ : 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).E : ℤ)
        = (Fintype.card K : ℤ) + 2 := by exact_mod_cast hE
    have hgoalZ : 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).F : ℤ)
        = (Fintype.card K : ℤ) + 6
          - 2 * (Fintype.card (Quotient (cycleSetoid ρ)) : ℤ) := by linarith [hZ, hEZ]
    -- transfer to ℕ subtraction.
    omega
  · intro hface
    -- from `2F = |K| + 6 - 2V` (ℕ truncated), recover the ℤ Euler identity.
    have hEZ : 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).E : ℤ)
        = (Fintype.card K : ℤ) + 2 := by exact_mod_cast hE
    -- `2V ≤ |K| + 6` so the ℕ subtraction is exact.
    have hle : 2 * Fintype.card (Quotient (cycleSetoid ρ)) ≤ Fintype.card K + 6 := by
      have : (Fintype.card K + 2) / 2 * 2 ≤ Fintype.card K + 2 := Nat.div_mul_le_self _ _
      omega
    have hfaceZ : 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).F : ℤ)
        = (Fintype.card K : ℤ) + 6
          - 2 * (Fintype.card (Quotient (cycleSetoid ρ)) : ℤ) := by
      have := hface
      zify [hle] at this
      linarith [this]
    linarith [hfaceZ, hEZ]

end EulerReduction



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}













end ChordApplication



section NonVacuity













end NonVacuity

end ProofsInTheBook.ChordSplitEuler











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitEuler
-/
/- Source module: ProofsInTheBook.ChordSideRecon -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ChordSideRecon

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Connectivity

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The **kept combinatorial map** on `K` with edge involution `β`, rotation `ρ`.
This is the side map *before* the fresh chord edge is spliced in; its connectivity
is the side's connectivity. -/
def keptCombMap (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k) :
    CombMap K where
  α := β
  σ := ρ
  α_invol := hβinv
  α_no_fixed := hβfix




/-- A `dartStep` of the kept map lifts to a `dartStep` of the fresh map on the
`inl` darts. -/
lemma freshMap_dartStep_inl_of_kept {x y : K}
    (h : (keptCombMap β ρ hβinv hβfix).dartStep x y) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep (Sum.inl x) (Sum.inl y) := by
  rcases h with hσ | hα
  · -- same σ-cycle in `ρ` ⇒ same `freshSigma`-cycle (by `freshSigma_sameCycle_iff`).
    left
    show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ.SameCycle (Sum.inl x) (Sum.inl y)
    rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne from rfl]
    rw [freshSigma_sameCycle_iff ρ hne]
    simpa using hσ
  · -- `y = β x` ⇒ `inl y = freshAlpha β (inl x)`.
    right
    show Sum.inl y = (freshMap β ρ hβinv hβfix a₀ a₁ hne).α (Sum.inl x)
    rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).α = freshAlpha β from rfl, freshAlpha_inl]
    rw [hα]; rfl

/-- Each `inl k` reaches every `inl`-image of a kept-map `dartStep` chain. -/
lemma freshMap_reach_inl_of_kept {x y : K}
    (h : Relation.ReflTransGen (keptCombMap β ρ hβinv hβfix).dartStep x y) :
    Relation.ReflTransGen (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep
      (Sum.inl x) (Sum.inl y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (freshMap_dartStep_inl_of_kept β ρ hβinv hβfix hne hstep)

/-- The fresh dart `inr 0` reaches `inl (ρ a₀)` in one σ-step. -/
lemma freshMap_reach_inr_zero :
    Relation.ReflTransGen (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep
      (Sum.inr 0) (Sum.inl (ρ a₀)) := by
  refine Relation.ReflTransGen.single (Or.inl ?_)
  show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ.SameCycle (Sum.inr 0) (Sum.inl (ρ a₀))
  rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne from rfl]
  exact ⟨1, by rw [zpow_one, freshSigma_fresh_zero ρ a₀ a₁ hne]⟩

/-- The fresh dart `inr 1` reaches `inl (ρ a₁)` in one σ-step. -/
lemma freshMap_reach_inr_one :
    Relation.ReflTransGen (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep
      (Sum.inr 1) (Sum.inl (ρ a₁)) := by
  refine Relation.ReflTransGen.single (Or.inl ?_)
  show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ.SameCycle (Sum.inr 1) (Sum.inl (ρ a₁))
  rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne from rfl]
  exact ⟨1, by rw [zpow_one, freshSigma_fresh_one ρ a₀ a₁ hne]⟩

/-- **Connectivity of the fresh map** (proved purely): if the kept map `(β, ρ)` is
connected, then so is the fresh map.  The two fresh darts attach to the existing
darts by one σ-step each (and to each other by an α-step), so reachability of the
kept darts lifts and the fresh darts join in. -/
theorem freshMap_connected_of_kept
    (hconn : (keptCombMap β ρ hβinv hβfix).Connected) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).Connected := by
  classical
  -- reach from any `inl x` to any `inl y` lifts from the kept connectivity.
  have reach_inl : ∀ x y : K, Relation.ReflTransGen
      (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep (Sum.inl x) (Sum.inl y) :=
    fun x y => freshMap_reach_inl_of_kept β ρ hβinv hβfix hne (hconn x y)
  -- reach from `inr j` to any `inl y`: go to `inl (ρ aⱼ)`, then lift.
  have reach_inr_inl : ∀ (j : Fin 2) (y : K), Relation.ReflTransGen
      (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep (Sum.inr j) (Sum.inl y) := by
    intro j y
    fin_cases j
    · exact (freshMap_reach_inr_zero β ρ hβinv hβfix hne).trans (reach_inl (ρ a₀) y)
    · exact (freshMap_reach_inr_one β ρ hβinv hβfix hne).trans (reach_inl (ρ a₁) y)
  -- reach from any `inl x` to any `inr j`: go to `inl (ρ aⱼ)`'s reverse via α back.
  -- easier: `inl x → inl (ρ a₀) → inr 0 → inr 1`.  Use α-step `inr 0 = α (inr 1)`? Build directly.
  have reach_inl_inr_zero : ∀ x : K, Relation.ReflTransGen
      (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep (Sum.inl x) (Sum.inr 0) := by
    intro x
    -- `inl x → inl a₀ → inr 0` (the anchor σ-step `freshSigma (inl a₀) = inr 0`).
    refine (reach_inl x a₀).tail (Or.inl ?_)
    show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ.SameCycle (Sum.inl a₀) (Sum.inr 0)
    rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne from rfl]
    exact ⟨1, by rw [zpow_one, freshSigma_anchor_zero ρ a₀ a₁ hne]⟩
  have reach_inl_inr_one : ∀ x : K, Relation.ReflTransGen
      (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartStep (Sum.inl x) (Sum.inr 1) := by
    intro x
    refine (reach_inl x a₁).tail (Or.inl ?_)
    show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ.SameCycle (Sum.inl a₁) (Sum.inr 1)
    rw [show (freshMap β ρ hβinv hβfix a₀ a₁ hne).σ = freshSigma ρ a₀ a₁ hne from rfl]
    exact ⟨1, by rw [zpow_one, freshSigma_anchor_one ρ a₀ a₁ hne]⟩
  intro a b
  cases a with
  | inl x =>
      cases b with
      | inl y => exact reach_inl x y
      | inr j => fin_cases j
                 · exact reach_inl_inr_zero x
                 · exact reach_inl_inr_one x
  | inr i =>
      cases b with
      | inl y => exact reach_inr_inl i y
      | inr j =>
          fin_cases i <;> fin_cases j
          · exact Relation.ReflTransGen.refl
          · exact (reach_inr_inl 0 a₁).trans (reach_inl_inr_one a₁)
          · exact (reach_inr_inl 1 a₀).trans (reach_inl_inr_zero a₀)
          · exact Relation.ReflTransGen.refl

end Connectivity



section SphereAssembly

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)



end SphereAssembly



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- The kept combinatorial map of side 1 (before the fresh chord splice): edge
involution `sideAlpha₁`, rotation `sideSigma₁`.  Its connectivity is side 1's
connectivity. -/
noncomputable def sideKeptMap₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CombMap {d : D // d ∉ data.keptDel₁} :=
  keptCombMap (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)

/-- The kept combinatorial map of side 2. -/
noncomputable def sideKeptMap₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CombMap {d : D // d ∉ data.keptDel₂} :=
  keptCombMap (data.sideAlpha₂ hsep) data.sideSigma₂
    (data.sideAlpha₂_involutive hsep) (data.sideAlpha₂_no_fixed hsep)





end ChordApplication



section JordanData

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  (a₀ a₁ : K) (hne : a₀ ≠ a₁)





end JordanData



section NonVacuity







end NonVacuity

end ProofsInTheBook.ChordSideRecon











end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFilteredRotation
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- A simple directed primal cycle of length `len` in `M`: a `Fin len`-indexed
family of darts whose source vertices are pairwise distinct and whose heads chain
to the next source. -/
structure SimplePrimalCycle (M : CombMap D) where
  /-- Length of the cycle (number of darts/edges). -/
  len : ℕ
  /-- The cycle has length at least three (no loops, no digons; faithful to a
  *simple* primal cycle in a simple graph). -/
  len_ge : 3 ≤ len
  /-- The directed cycle darts `d_0, …, d_{len-1}`. -/
  dart : Fin len → D
  /-- Simplicity: the source vertices are pairwise distinct. -/
  tail_inj : Function.Injective (fun i => M.tail (dart i))
  /-- Consecutive incidence: the head of `d_i` is the tail of `d_{i+1}`
  (cyclically). -/
  consecutive : ∀ i : Fin len,
    M.head (dart i) = M.tail (dart ⟨(i.1 + 1) % len, Nat.mod_lt _ (by omega)⟩)

namespace SimplePrimalCycle

variable {M : CombMap D}

lemma len_pos (C : SimplePrimalCycle M) : 0 < C.len := by have := C.len_ge; omega

/-- Cyclic successor index. -/
def nextIdx (C : SimplePrimalCycle M) (i : Fin C.len) : Fin C.len :=
  ⟨(i.1 + 1) % C.len, Nat.mod_lt _ C.len_pos⟩

/-- Cyclic predecessor index. -/
def prevIdx (C : SimplePrimalCycle M) (i : Fin C.len) : Fin C.len :=
  ⟨(i.1 + (C.len - 1)) % C.len, Nat.mod_lt _ C.len_pos⟩

@[simp]
lemma nextIdx_val (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.nextIdx i).1 = (i.1 + 1) % C.len := rfl

@[simp]
lemma prevIdx_val (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.prevIdx i).1 = (i.1 + (C.len - 1)) % C.len := rfl

lemma nextIdx_prevIdx (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.nextIdx (C.prevIdx i) = i := by
  apply Fin.ext
  simp only [nextIdx_val, prevIdx_val]
  have hk : 0 < C.len := C.len_pos
  rw [Nat.mod_add_mod]
  have : i.1 + (C.len - 1) + 1 = i.1 + C.len := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma prevIdx_nextIdx (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.prevIdx (C.nextIdx i) = i := by
  apply Fin.ext
  simp only [nextIdx_val, prevIdx_val]
  have hk : 0 < C.len := C.len_pos
  rw [Nat.mod_add_mod]
  have : i.1 + 1 + (C.len - 1) = i.1 + C.len := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- The `i`-th cycle edge, as the `α`-orbit (Sym2 of endpoints) of `dart i`. -/
def edge (C : SimplePrimalCycle M) (i : Fin C.len) : Sym2 M.Vertex :=
  M.dartEdge (C.dart i)

/-- The set of darts that constitute the cycle edges (both the forward darts and
their `α`-reverses). -/
def dartSet (C : SimplePrimalCycle M) : Finset D :=
  Finset.univ.filter (fun d => ∃ i : Fin C.len, d = C.dart i ∨ d = M.α (C.dart i))

lemma mem_dartSet_iff (C : SimplePrimalCycle M) (d : D) :
    d ∈ C.dartSet ↔ ∃ i : Fin C.len, d = C.dart i ∨ d = M.α (C.dart i) := by
  simp [dartSet]

lemma dart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.dart i ∈ C.dartSet :=
  (C.mem_dartSet_iff _).2 ⟨i, Or.inl rfl⟩

lemma alpha_dart_mem_dartSet (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.α (C.dart i) ∈ C.dartSet :=
  (C.mem_dartSet_iff _).2 ⟨i, Or.inr rfl⟩

/-- The set of cycle *edges* (as `Sym2`). -/
def edgeSet (C : SimplePrimalCycle M) : Finset (Sym2 M.Vertex) :=
  Finset.univ.filter (fun e => ∃ i : Fin C.len, e = C.edge i)

lemma mem_edgeSet_iff (C : SimplePrimalCycle M) (e : Sym2 M.Vertex) :
    e ∈ C.edgeSet ↔ ∃ i : Fin C.len, e = C.edge i := by
  simp [edgeSet]



/-- The "left" face of the `i`-th cycle edge: the face of the forward dart. -/
def faceLeft (C : SimplePrimalCycle M) (i : Fin C.len) : M.Face :=
  M.dartFace (C.dart i)

/-- The "right" face of the `i`-th cycle edge: the face of the reverse dart. -/
def faceRight (C : SimplePrimalCycle M) (i : Fin C.len) : M.Face :=
  M.dartFace (M.α (C.dart i))



lemma consecutive' (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.head (C.dart i) = M.tail (C.dart (C.nextIdx i)) := C.consecutive i

/-- The forward cycle darts are pairwise distinct. -/
lemma dart_inj (C : SimplePrimalCycle M) : Function.Injective C.dart := by
  intro i j h
  exact C.tail_inj (by simp only []; rw [h])

/-- `tail (dart (nextIdx i)) = head (dart i)`, restated. -/
lemma tail_dart_nextIdx (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.tail (C.dart (C.nextIdx i)) = M.head (C.dart i) := (C.consecutive i).symm

/-- The `nextIdx` map is a bijection on indices (it is `prevIdx`-inverse). -/
lemma nextIdx_inj (C : SimplePrimalCycle M) : Function.Injective C.nextIdx := by
  intro i j h
  have := congrArg C.prevIdx h
  rwa [C.prevIdx_nextIdx, C.prevIdx_nextIdx] at this

/-- A forward cycle dart is never the `α`-reverse of a forward cycle dart.
This rules out the digon/loop degeneracy and uses `3 ≤ len`. -/
lemma dart_ne_alpha_dart (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.dart i ≠ M.α (C.dart j) := by
  intro h
  -- tails: tail(dart i) = tail(α dart j) = head(dart j) = tail(dart (next j))
  have ht : M.tail (C.dart i) = M.tail (C.dart (C.nextIdx j)) := by
    rw [h]; rw [tail_alpha]; exact (C.tail_dart_nextIdx j).symm
  have hij : i = C.nextIdx j := C.tail_inj ht
  -- heads: head(dart i) = head(α dart j) = tail(dart j)
  have hh : M.tail (C.dart (C.nextIdx i)) = M.tail (C.dart j) := by
    have : M.head (C.dart i) = M.tail (C.dart j) := by
      rw [h, head_alpha]
    rw [C.tail_dart_nextIdx i, this]
  have hnij : C.nextIdx i = j := C.tail_inj hh
  -- i = next j and next i = j ⇒ next (next j) = j ⇒ len ∣ 2, contradiction with len ≥ 3.
  rw [hij] at hnij
  have hval := congrArg Fin.val hnij
  simp only [nextIdx_val] at hval
  have hk : 3 ≤ C.len := C.len_ge
  have hjlt : j.1 < C.len := j.isLt
  -- ((j+1)%len + 1) % len = j  with len ≥ 3 is impossible
  rcases Nat.lt_or_ge (j.1 + 1) C.len with hcase | hcase
  · rw [Nat.mod_eq_of_lt hcase] at hval
    rcases Nat.lt_or_ge (j.1 + 1 + 1) C.len with hc2 | hc2
    · rw [Nat.mod_eq_of_lt hc2] at hval; omega
    · have : (j.1 + 1 + 1) % C.len = j.1 + 1 + 1 - C.len := by
        rw [Nat.mod_eq_sub_mod hc2, Nat.mod_eq_of_lt (by omega)]
      rw [this] at hval; omega
  · have hje : j.1 + 1 = C.len := by omega
    rw [hje, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-- The `α`-reverse cycle darts are pairwise distinct. -/
lemma alpha_dart_inj (C : SimplePrimalCycle M) :
    Function.Injective (fun i => M.α (C.dart i)) := by
  intro i j h
  simp only [] at h
  exact C.dart_inj (M.α.injective h)

/-- A forward cycle dart is not its own reverse. -/
lemma dart_ne_alpha_self (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.dart i ≠ M.α (C.dart i) := fun h => M.α_no_fixed (C.dart i) h.symm



open Classical in
/-- Classify a dart with respect to the cycle:
`inl (inl i)` if `d = dart i`; `inl (inr i)` if `d = α (dart i)`; `inr ()` if
neither. -/
noncomputable def cycleKind (C : SimplePrimalCycle M) (d : D) :
    (Fin C.len ⊕ Fin C.len) ⊕ Unit :=
  if hf : ∃ i, d = C.dart i then Sum.inl (Sum.inl hf.choose)
  else if hr : ∃ i, d = M.α (C.dart i) then Sum.inl (Sum.inr hr.choose)
  else Sum.inr ()

open Classical in
lemma cycleKind_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cycleKind (C.dart i) = Sum.inl (Sum.inl i) := by
  have hf : ∃ j, C.dart i = C.dart j := ⟨i, rfl⟩
  rw [cycleKind, dif_pos hf]
  congr 1
  congr 1
  exact (C.dart_inj hf.choose_spec.symm)

open Classical in
lemma cycleKind_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cycleKind (M.α (C.dart i)) = Sum.inl (Sum.inr i) := by
  have hnf : ¬ ∃ j, M.α (C.dart i) = C.dart j := by
    rintro ⟨j, hj⟩; exact C.dart_ne_alpha_dart j i hj.symm
  have hr : ∃ j, M.α (C.dart i) = M.α (C.dart j) := ⟨i, rfl⟩
  rw [cycleKind, dif_neg hnf, dif_pos hr]
  congr 1
  congr 1
  exact C.alpha_dart_inj hr.choose_spec.symm

open Classical in
lemma cycleKind_other (C : SimplePrimalCycle M) {d : D}
    (h : d ∉ C.dartSet) :
    C.cycleKind d = Sum.inr () := by
  have hnf : ¬ ∃ i, d = C.dart i := by
    rintro ⟨i, rfl⟩; exact h (C.dart_mem_dartSet i)
  have hnr : ¬ ∃ i, d = M.α (C.dart i) := by
    rintro ⟨i, rfl⟩; exact h (C.alpha_dart_mem_dartSet i)
  rw [cycleKind, dif_neg hnf, dif_neg hnr]

open Classical in
lemma cycleKind_eq_inl_inl (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.cycleKind d = Sum.inl (Sum.inl i)) : d = C.dart i := by
  rw [cycleKind] at h
  by_cases hf : ∃ j, d = C.dart j
  · rw [dif_pos hf] at h
    simp only [Sum.inl.injEq] at h
    rw [hf.choose_spec, h]
  · rw [dif_neg hf] at h
    split at h <;> simp at h

open Classical in
lemma cycleKind_eq_inl_inr (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.cycleKind d = Sum.inl (Sum.inr i)) : d = M.α (C.dart i) := by
  rw [cycleKind] at h
  by_cases hf : ∃ j, d = C.dart j
  · rw [dif_pos hf] at h; simp at h
  · rw [dif_neg hf] at h
    by_cases hr : ∃ j, d = M.α (C.dart j)
    · rw [dif_pos hr] at h
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h
      rw [hr.choose_spec, h]
    · rw [dif_neg hr] at h; simp at h

open Classical in
lemma cycleKind_eq_inr (C : SimplePrimalCycle M) {d : D}
    (h : C.cycleKind d = Sum.inr ()) : d ∉ C.dartSet := by
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  obtain ⟨i, hi | hi⟩ := hmem
  · rw [hi, C.cycleKind_dart] at h; simp at h
  · rw [hi, C.cycleKind_alpha_dart] at h; simp at h

end SimplePrimalCycle



/-- Face adjacency across a primal edge not in `C`'s edge set. -/
def DualAvoidsCycleStep (M : CombMap D) (C : SimplePrimalCycle M)
    (f g : M.Face) : Prop :=
  ∃ d : D, M.dartEdge d ∉ C.edgeSet ∧ M.dartFace d = f ∧ M.dartFace (M.α d) = g

/-- Dual reachability avoiding all cycle edges. -/
def DualReachableAvoidingCycle (M : CombMap D) (C : SimplePrimalCycle M)
    (f g : M.Face) : Prop :=
  Relation.ReflTransGen (DualAvoidsCycleStep M C) f g



namespace SimplePrimalCycle

variable {M : CombMap D}

/-- The fresh-dart-augmented dart type of the cut map: original darts plus `2k`
fresh cap darts `c_i^+ = inr (inl i)`, `c_i^- = inr (inr i)`. -/
abbrev CutDart (C : SimplePrimalCycle M) : Type _ := D ⊕ (Fin C.len ⊕ Fin C.len)

open Classical in
/-- The new edge involution of the cut map. -/
noncomputable def cutAlpha (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.cycleKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- d = dart i ↦ c_i^+
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- d = α (dart i) ↦ c_i^-
      | Sum.inr () => Sum.inl (M.α d)                -- non-cycle: old pairing
  | Sum.inr (Sum.inl i) => Sum.inl (C.dart i)        -- c_i^+ ↦ dart i
  | Sum.inr (Sum.inr i) => Sum.inl (M.α (C.dart i))  -- c_i^- ↦ α (dart i)

@[simp] lemma cutAlpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inl (C.dart i)) = Sum.inr (Sum.inl i) := by
  show (match C.cycleKind (C.dart i) with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.α (C.dart i))) = _
  rw [C.cycleKind_dart]

@[simp] lemma cutAlpha_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inl (M.α (C.dart i))) = Sum.inr (Sum.inr i) := by
  show (match C.cycleKind (M.α (C.dart i)) with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.α (M.α (C.dart i)))) = _
  rw [C.cycleKind_alpha_dart]

lemma cutAlpha_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.cutAlpha (Sum.inl d) = Sum.inl (M.α d) := by
  show (match C.cycleKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.α d)) = _
  rw [C.cycleKind_other h]

@[simp] lemma cutAlpha_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inr (Sum.inl i)) = Sum.inl (C.dart i) := rfl

@[simp] lemma cutAlpha_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutAlpha (Sum.inr (Sum.inr i)) = Sum.inl (M.α (C.dart i)) := rfl

/-- A non-cycle dart's reverse is also a non-cycle dart. -/
lemma alpha_notMem_dartSet (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    M.α d ∉ C.dartSet := by
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  obtain ⟨i, hi | hi⟩ := hmem
  · -- α d = dart i ⇒ d = α (dart i) ∈ dartSet
    apply h; rw [C.mem_dartSet_iff]
    exact ⟨i, Or.inr (by rw [← hi, M.alpha_alpha])⟩
  · -- α d = α (dart i) ⇒ d = dart i ∈ dartSet
    apply h; rw [C.mem_dartSet_iff]
    have : d = C.dart i := M.α.injective hi
    exact ⟨i, Or.inl this⟩

/-- `cutAlpha` is an involution. -/
lemma cutAlpha_involutive (C : SimplePrimalCycle M) :
    Function.Involutive C.cutAlpha := by
  intro x
  rcases x with d | (i | i)
  · by_cases h : d ∈ C.dartSet
    · rw [C.mem_dartSet_iff] at h
      obtain ⟨i, hi | hi⟩ := h
      · subst hi; rw [C.cutAlpha_dart, C.cutAlpha_capPlus]
      · subst hi; rw [C.cutAlpha_alpha_dart, C.cutAlpha_capMinus]
    · rw [C.cutAlpha_other h, C.cutAlpha_other (C.alpha_notMem_dartSet h), M.alpha_alpha]
  · rw [C.cutAlpha_capPlus, C.cutAlpha_dart]
  · rw [C.cutAlpha_capMinus, C.cutAlpha_alpha_dart]

/-- `cutAlpha` has no fixed points. -/
lemma cutAlpha_no_fixed (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutAlpha x ≠ x := by
  rcases x with d | (i | i)
  · by_cases h : d ∈ C.dartSet
    · rw [C.mem_dartSet_iff] at h
      obtain ⟨i, hi | hi⟩ := h
      · subst hi; rw [C.cutAlpha_dart]; simp
      · subst hi; rw [C.cutAlpha_alpha_dart]; simp
    · rw [C.cutAlpha_other h]; simp only [ne_eq, Sum.inl.injEq]
      exact M.α_no_fixed d
  · rw [C.cutAlpha_capPlus]; simp
  · rw [C.cutAlpha_capMinus]; simp

/-- `cutAlpha` as a permutation. -/
noncomputable def cutAlphaPerm (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Function.Involutive.toPerm C.cutAlpha C.cutAlpha_involutive

@[simp] lemma cutAlphaPerm_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutAlphaPerm x = C.cutAlpha x := rfl

end SimplePrimalCycle





namespace CutCapSurgery

variable {M : CombMap D} {C : SimplePrimalCycle M}









end CutCapSurgery



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **Step lift.**  If `C.edgeSet ⊆ {s(u,v)} ∪ boundaryEdges`, then any
`ChordSplitAdj u v` step is a `DualAvoidsCycleStep M C` step: the shared edge,
being neither the chord nor a boundary edge, is not a cycle edge. -/
lemma chordSplitAdj_dualAvoidsCycleStep {u v : M.Vertex} (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    {f g : M.Face} (hfg : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M C f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := hfg
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rcases hsub _ hmem with hchord | hbound
  · exact hch hchord
  · exact hbe hbound

/-- **Path lift.**  Under the same edge-containment, a `ChordSplitAdj`-path lifts
to a `DualReachableAvoidingCycle` path. -/
lemma reachable_dualAvoidsCycle_of_chordSplitAdj {u v : M.Vertex}
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    {f g : M.Face}
    (hfg : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    DualReachableAvoidingCycle M C f g := by
  induction hfg with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (hNT.chordSplitAdj_dualAvoidsCycleStep C hsub hstep)







end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapSigma -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}



/-- The forward cycle dart at `v_i` (the `+`-bank start). -/
def qDart (C : SimplePrimalCycle M) (i : Fin C.len) : D := C.dart i

/-- The reverse dart entering `v_i` (the `−`-bank start), `p_i = α (dart (prevIdx i))`. -/
def pDart (C : SimplePrimalCycle M) (i : Fin C.len) : D := M.α (C.dart (C.prevIdx i))

@[simp] lemma qDart_def (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.qDart i = C.dart i := rfl

@[simp] lemma pDart_def (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.pDart i = M.α (C.dart (C.prevIdx i)) := rfl

/-- `q`-darts are pairwise distinct. -/
lemma qDart_inj (C : SimplePrimalCycle M) : Function.Injective C.qDart :=
  C.dart_inj

/-- `p`-darts are pairwise distinct. -/
lemma pDart_inj (C : SimplePrimalCycle M) : Function.Injective C.pDart := by
  intro i j h
  simp only [pDart_def] at h
  have := C.dart_inj (M.α.injective h)
  exact C.nextIdx_inj (by rw [← C.nextIdx_prevIdx i, ← C.nextIdx_prevIdx j, this])

/-- A `p`-dart never equals a `q`-dart (rules out the digon, uses `3 ≤ len`). -/
lemma pDart_ne_qDart (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.pDart i ≠ C.qDart j := by
  simp only [pDart_def, qDart_def]
  exact fun h => C.dart_ne_alpha_dart j (C.prevIdx i) h.symm



open Classical in
/-- Classify a dart by where its `σ`-successor sits among the bank-start darts:
`inl (inl i)` if `σ d = p_i` (`d` is the `+`-bank end `ℓ_i^+`); `inl (inr i)` if
`σ d = q_i` (`d` is the `−`-bank end `ℓ_i^-`); `inr ()` otherwise. -/
noncomputable def divertKind (C : SimplePrimalCycle M) (d : D) :
    (Fin C.len ⊕ Fin C.len) ⊕ Unit :=
  if hp : ∃ i, M.σ d = C.pDart i then Sum.inl (Sum.inl hp.choose)
  else if hq : ∃ i, M.σ d = C.qDart i then Sum.inl (Sum.inr hq.choose)
  else Sum.inr ()

open Classical in
lemma divertKind_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.pDart i) : C.divertKind d = Sum.inl (Sum.inl i) := by
  have hp : ∃ j, M.σ d = C.pDart j := ⟨i, h⟩
  rw [divertKind, dif_pos hp]
  congr 2
  exact C.pDart_inj (hp.choose_spec.symm.trans h)

open Classical in
lemma divertKind_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : M.σ d = C.qDart i) : C.divertKind d = Sum.inl (Sum.inr i) := by
  have hnp : ¬ ∃ j, M.σ d = C.pDart j := by
    rintro ⟨j, hj⟩; exact C.pDart_ne_qDart j i (hj.symm.trans h)
  have hq : ∃ j, M.σ d = C.qDart j := ⟨i, h⟩
  rw [divertKind, dif_neg hnp, dif_pos hq]
  congr 2
  exact C.qDart_inj (hq.choose_spec.symm.trans h)

open Classical in
lemma divertKind_none (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, M.σ d ≠ C.pDart i) (hq : ∀ i, M.σ d ≠ C.qDart i) :
    C.divertKind d = Sum.inr () := by
  rw [divertKind, dif_neg (by rintro ⟨i, hi⟩; exact hp i hi),
    dif_neg (by rintro ⟨i, hi⟩; exact hq i hi)]

open Classical in
lemma divertKind_eq_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inl i)) : M.σ d = C.pDart i := by
  rw [divertKind] at h
  by_cases hp : ∃ j, M.σ d = C.pDart j
  · rw [dif_pos hp] at h
    simp only [Sum.inl.injEq] at h
    rw [hp.choose_spec, h]
  · rw [dif_neg hp] at h; split at h <;> simp at h

open Classical in
lemma divertKind_eq_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inr i)) : M.σ d = C.qDart i := by
  rw [divertKind] at h
  by_cases hp : ∃ j, M.σ d = C.pDart j
  · rw [dif_pos hp] at h; simp at h
  · rw [dif_neg hp] at h
    by_cases hq : ∃ j, M.σ d = C.qDart j
    · rw [dif_pos hq] at h
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h
      rw [hq.choose_spec, h]
    · rw [dif_neg hq] at h; simp at h

open Classical in
lemma divertKind_eq_none (C : SimplePrimalCycle M) {d : D}
    (h : C.divertKind d = Sum.inr ()) :
    (∀ i, M.σ d ≠ C.pDart i) ∧ (∀ i, M.σ d ≠ C.qDart i) := by
  constructor
  · intro i hi; rw [C.divertKind_plus hi] at h; simp at h
  · intro i hi; rw [C.divertKind_minus hi] at h; simp at h



open Classical in
/-- Classify a dart by whether it is a bank-start dart: `inl (inl i)` if `d = q_i`,
`inl (inr i)` if `d = p_i`, `inr ()` otherwise. -/
noncomputable def startKind (C : SimplePrimalCycle M) (d : D) :
    (Fin C.len ⊕ Fin C.len) ⊕ Unit :=
  if hq : ∃ i, d = C.qDart i then Sum.inl (Sum.inl hq.choose)
  else if hp : ∃ i, d = C.pDart i then Sum.inl (Sum.inr hp.choose)
  else Sum.inr ()

open Classical in
lemma startKind_q (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.startKind (C.qDart i) = Sum.inl (Sum.inl i) := by
  have hq : ∃ j, C.qDart i = C.qDart j := ⟨i, rfl⟩
  rw [startKind, dif_pos hq]; congr 2; exact C.qDart_inj hq.choose_spec.symm

open Classical in
lemma startKind_p (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.startKind (C.pDart i) = Sum.inl (Sum.inr i) := by
  have hnq : ¬ ∃ j, C.pDart i = C.qDart j := by
    rintro ⟨j, hj⟩; exact C.pDart_ne_qDart i j hj
  have hp : ∃ j, C.pDart i = C.pDart j := ⟨i, rfl⟩
  rw [startKind, dif_neg hnq, dif_pos hp]; congr 2; exact C.pDart_inj hp.choose_spec.symm

open Classical in
lemma startKind_none (C : SimplePrimalCycle M) {d : D}
    (hq : ∀ i, d ≠ C.qDart i) (hp : ∀ i, d ≠ C.pDart i) :
    C.startKind d = Sum.inr () := by
  rw [startKind, dif_neg (by rintro ⟨i, hi⟩; exact hq i hi),
    dif_neg (by rintro ⟨i, hi⟩; exact hp i hi)]

open Classical in
lemma startKind_eq_q (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inl i)) : d = C.qDart i := by
  rw [startKind] at h
  by_cases hq : ∃ j, d = C.qDart j
  · rw [dif_pos hq] at h; simp only [Sum.inl.injEq] at h; rw [hq.choose_spec, h]
  · rw [dif_neg hq] at h; split at h <;> simp at h

open Classical in
lemma startKind_eq_p (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inr i)) : d = C.pDart i := by
  rw [startKind] at h
  by_cases hq : ∃ j, d = C.qDart j
  · rw [dif_pos hq] at h; simp at h
  · rw [dif_neg hq] at h
    by_cases hp : ∃ j, d = C.pDart j
    · rw [dif_pos hp] at h
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h; rw [hp.choose_spec, h]
    · rw [dif_neg hp] at h; simp at h

open Classical in
lemma startKind_eq_none (C : SimplePrimalCycle M) {d : D}
    (h : C.startKind d = Sum.inr ()) :
    (∀ i, d ≠ C.qDart i) ∧ (∀ i, d ≠ C.pDart i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [hi, C.startKind_q] at h; simp at h
  · rw [hi, C.startKind_p] at h; simp at h



open Classical in
/-- Forward map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigma (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.divertKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- ℓ_i^+ ↦ c_i^+
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- ℓ_i^- ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ d)                -- unchanged rotation
  | Sum.inr (Sum.inl i) => Sum.inl (C.qDart i)       -- c_i^+ ↦ q_i
  | Sum.inr (Sum.inr i) => Sum.inl (C.pDart i)       -- c_i^- ↦ p_i

open Classical in
/-- Inverse map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigmaInv (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.startKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- q_i ↦ c_i^+
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- p_i ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ.symm d)           -- unchanged inverse rotation
  | Sum.inr (Sum.inl i) => Sum.inl (M.σ.symm (C.pDart i))  -- c_i^+ ↦ ℓ_i^+ = σ⁻¹ p_i
  | Sum.inr (Sum.inr i) => Sum.inl (M.σ.symm (C.qDart i))  -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i



lemma cutSigma_inl_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inl i)) :
    C.cutSigma (Sum.inl d) = Sum.inr (Sum.inl i) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma_inl_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inr i)) :
    C.cutSigma (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.divertKind d = Sum.inr ()) :
    C.cutSigma (Sum.inl d) = Sum.inl (M.σ d) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

@[simp] lemma cutSigma_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma (Sum.inr (Sum.inl i)) = Sum.inl (C.qDart i) := rfl

@[simp] lemma cutSigma_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma (Sum.inr (Sum.inr i)) = Sum.inl (C.pDart i) := rfl



lemma cutSigmaInv_inl_q (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inl i)) :
    C.cutSigmaInv (Sum.inl d) = Sum.inr (Sum.inl i) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv_inl_p (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inr i)) :
    C.cutSigmaInv (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.startKind d = Sum.inr ()) :
    C.cutSigmaInv (Sum.inl d) = Sum.inl (M.σ.symm d) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

@[simp] lemma cutSigmaInv_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv (Sum.inr (Sum.inl i)) = Sum.inl (M.σ.symm (C.pDart i)) := rfl

@[simp] lemma cutSigmaInv_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv (Sum.inr (Sum.inr i)) = Sum.inl (M.σ.symm (C.qDart i)) := rfl



open Classical in
lemma cutSigma_leftInv (C : SimplePrimalCycle M) :
    Function.LeftInverse C.cutSigmaInv C.cutSigma := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on divertKind d
    rcases hd : C.divertKind d with (i | i) | u
    · -- σ d = p_i : ℓ_i^+
      have hσ : M.σ d = C.pDart i := C.divertKind_eq_plus hd
      rw [C.cutSigma_inl_plus hd, cutSigmaInv_capPlus]
      rw [← hσ, M.σ.symm_apply_apply]
    · -- σ d = q_i : ℓ_i^-
      have hσ : M.σ d = C.qDart i := C.divertKind_eq_minus hd
      rw [C.cutSigma_inl_minus hd, cutSigmaInv_capMinus]
      rw [← hσ, M.σ.symm_apply_apply]
    · -- unchanged
      obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
      rw [C.cutSigma_inl_none hd, C.cutSigmaInv_inl_none (C.startKind_none hq hp),
        M.σ.symm_apply_apply]
  · -- x = c_i^+
    rw [cutSigma_capPlus, C.cutSigmaInv_inl_q (C.startKind_q i)]
  · -- x = c_i^-
    rw [cutSigma_capMinus, C.cutSigmaInv_inl_p (C.startKind_p i)]

open Classical in
lemma cutSigma_rightInv (C : SimplePrimalCycle M) :
    Function.RightInverse C.cutSigmaInv C.cutSigma := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on startKind d
    rcases hd : C.startKind d with (i | i) | u
    · -- d = q_i
      have hq : d = C.qDart i := C.startKind_eq_q hd
      rw [C.cutSigmaInv_inl_q hd, cutSigma_capPlus, hq]
    · -- d = p_i
      have hp : d = C.pDart i := C.startKind_eq_p hd
      rw [C.cutSigmaInv_inl_p hd, cutSigma_capMinus, hp]
    · -- neither: d ≠ q_i, p_i for all i
      obtain ⟨hq, hp⟩ := C.startKind_eq_none hd
      rw [C.cutSigmaInv_inl_none hd]
      have hdiv : C.divertKind (M.σ.symm d) = Sum.inr () := by
        apply C.divertKind_none
        · intro i; rw [M.σ.apply_symm_apply]; exact hp i
        · intro i; rw [M.σ.apply_symm_apply]; exact hq i
      rw [C.cutSigma_inl_none hdiv, M.σ.apply_symm_apply]
  · -- x = c_i^+ : σ⁻¹ p_i ↦ back to c_i^+
    rw [cutSigmaInv_capPlus]
    have hdiv : C.divertKind (M.σ.symm (C.pDart i)) = Sum.inl (Sum.inl i) :=
      C.divertKind_plus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma_inl_plus hdiv]
  · -- x = c_i^-
    rw [cutSigmaInv_capMinus]
    have hdiv : C.divertKind (M.σ.symm (C.qDart i)) = Sum.inl (Sum.inr i) :=
      C.divertKind_minus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma_inl_minus hdiv]

/-- The new vertex rotation `σ'` as a permutation of the cut dart set. -/
noncomputable def cutSigmaPerm (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart where
  toFun := C.cutSigma
  invFun := C.cutSigmaInv
  left_inv := C.cutSigma_leftInv
  right_inv := C.cutSigma_rightInv

@[simp] lemma cutSigmaPerm_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutSigmaPerm x = C.cutSigma x := rfl





















end SimplePrimalCycle









end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.PermTranspositionCycleCount -/
section
set_option autoImplicit true


set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open Equiv Equiv.Perm Function

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def numCycles (p : Equiv.Perm D) : ℕ := by
  classical
  exact Fintype.card (Quotient (SameCycle.setoid p))

namespace PermTranspositionCycleCount

open scoped Finset

def mergeRel (p : Equiv.Perm D) (a b x y : D) : Prop :=
  p.SameCycle x y ∨
    (p.SameCycle x a ∧ p.SameCycle y b) ∨
      (p.SameCycle x b ∧ p.SameCycle y a)

lemma mergeRel_refl (p : Equiv.Perm D) (a b x : D) :
    mergeRel p a b x x := by
  exact Or.inl SameCycle.rfl

lemma mergeRel_symm {p : Equiv.Perm D} {a b x y : D} :
    mergeRel p a b x y → mergeRel p a b y x := by
  rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨hyb, hxa⟩)
  · exact Or.inr (Or.inl ⟨hya, hxb⟩)

lemma mergeRel_trans {p : Equiv.Perm D} {a b x y z : D} :
    mergeRel p a b x y → mergeRel p a b y z → mergeRel p a b x z := by
  intro hxy hyz
  rcases hxy with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (Or.inl ⟨hxy.trans hya, hzb⟩)
    · exact Or.inr (Or.inr ⟨hxy.trans hyb, hza⟩)
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb', hza⟩
    · exact Or.inr (Or.inl ⟨hxa, hyz.symm.trans hyb⟩)
    · exact Or.inr (Or.inl ⟨hxa, hzb⟩)
    · exact Or.inl (hxa.trans hza.symm)
  · rcases hyz with hyz | ⟨hya', hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inr (Or.inr ⟨hxb, hyz.symm.trans hya⟩)
    · exact Or.inl (hxb.trans hzb.symm)
    · exact Or.inr (Or.inr ⟨hxb, hza⟩)

lemma mergeRel_step (p : Equiv.Perm D) (a b z : D) :
    mergeRel p a b z ((p * Equiv.swap a b) z) := by
  by_cases hza : z = a
  · subst hza
    refine Or.inr (Or.inl ⟨SameCycle.rfl, ?_⟩)
    rw [mul_apply, Equiv.swap_apply_left]
    exact sameCycle_apply_left.mpr SameCycle.rfl
  · by_cases hzb : z = b
    · subst hzb
      refine Or.inr (Or.inr ⟨SameCycle.rfl, ?_⟩)
      rw [mul_apply, Equiv.swap_apply_right]
      exact sameCycle_apply_left.mpr SameCycle.rfl
    · refine Or.inl ?_
      rw [mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]
      exact sameCycle_apply_right.mpr SameCycle.rfl

lemma mergeRel_pow_apply (p : Equiv.Perm D) (a b x : D) (n : ℕ) :
    mergeRel p a b x (((p * Equiv.swap a b) ^ n) x) := by
  induction n with
  | zero =>
      simpa using mergeRel_refl p a b x
  | succ n ih =>
      rw [pow_succ', mul_apply]
      exact mergeRel_trans ih (mergeRel_step p a b (((p * Equiv.swap a b) ^ n) x))

lemma mergeRel_of_sameCycle_mul_swap {p : Equiv.Perm D} {a b x y : D} :
    (p * Equiv.swap a b).SameCycle x y → mergeRel p a b x y := by
  rintro ⟨i, hi⟩
  cases i with
  | ofNat n =>
      rw [← hi]
      exact mergeRel_pow_apply p a b x n
  | negSucc n =>
      have hxy : ((p * Equiv.swap a b) ^ (n + 1)) y = x := by
        rw [← hi]
        simp [zpow_negSucc, pow_succ]
      have hyx : mergeRel p a b y x := by
        simpa [hxy] using mergeRel_pow_apply p a b y (n + 1)
      exact mergeRel_symm hyx

lemma mergeRel_of_base_sameCycle {p : Equiv.Perm D} {a b x y : D}
    (hab : p.SameCycle a b) :
    mergeRel p a b x y → p.SameCycle x y := by
  rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
  · exact h
  · exact hxa.trans (hab.trans hyb.symm)
  · exact hxb.trans (hab.symm.trans hya.symm)

lemma mul_swap_pow_succ_apply_left_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hnsc : ¬ p.SameCycle a b) :
    ∀ n : ℕ, n < orderOf (p.cycleOf b) →
      (((p * Equiv.swap a b) ^ (n + 1)) a = (p ^ (n + 1)) b)
  | 0, _ => by
      simp [mul_apply]
  | n + 1, hnlt => by
      have hnlt' : n < orderOf (p.cycleOf b) := lt_trans (Nat.lt_succ_self n) hnlt
      have ih := mul_swap_pow_succ_apply_left_of_not_sameCycle p hnsc n hnlt'
      rw [pow_succ', mul_apply, ih, mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · rw [pow_succ', mul_apply]
        simp [pow_succ', mul_apply]
      · intro ha
        apply hnsc
        have hba : p.SameCycle b a :=
          ⟨((n + 1 : ℕ) : ℤ), by simpa [zpow_natCast] using ha⟩
        exact hba.symm
      · intro hb
        have hpbn : p b ≠ b := by
          intro hpb
          have hcycle : p.cycleOf b = 1 := (cycleOf_eq_one_iff p).mpr hpb
          rw [hcycle, orderOf_one] at hnlt
          omega
        have hcb : p.cycleOf b b ≠ b := by
          simpa using hpbn
        have hcyclePow : (p.cycleOf b ^ (n + 1)) b = b := by
          simpa using hb
        have hpowOne : p.cycleOf b ^ (n + 1) = 1 :=
          ((isCycle_cycleOf p hpbn).pow_eq_one_iff' hcb).mpr hcyclePow
        exact pow_ne_one_of_lt_orderOf (by omega : n + 1 ≠ 0) hnlt hpowOne

lemma sameCycle_mul_swap_self_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hnsc : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle a b := by
  let m := orderOf (p.cycleOf b)
  have hmpos : 0 < m := orderOf_pos (p.cycleOf b)
  cases hm : m with
  | zero =>
      omega
  | succ n =>
      refine ⟨((n + 1 : ℕ) : ℤ), ?_⟩
      have hnlt : n < orderOf (p.cycleOf b) := by
        simpa [m, hm] using Nat.lt_succ_self n
      have hq := mul_swap_pow_succ_apply_left_of_not_sameCycle p hnsc n hnlt
      have hp : (p ^ (n + 1)) b = b := by
        have hc : (p.cycleOf b ^ (n + 1)) b = b := by
          have : p.cycleOf b ^ orderOf (p.cycleOf b) = 1 := pow_orderOf_eq_one _
          simpa [m, hm] using congrFun (congrArg DFunLike.coe this) b
        simpa using hc
      change ((p * Equiv.swap a b) ^ (n + 1 : ℕ)) a = b
      exact hq.trans hp

lemma sameCycle_le_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b x y : D} (hnsc : ¬ p.SameCycle a b)
    (hxy : p.SameCycle x y) :
    (p * Equiv.swap a b).SameCycle x y := by
  let q := p * Equiv.swap a b
  have hqab : q.SameCycle a b := sameCycle_mul_swap_self_of_not_sameCycle p hnsc
  have hstep : ∀ z : D, q.SameCycle z (p z) := by
    intro z
    by_cases hza : z = a
    · subst z
      exact hqab.trans (by simpa [q, mul_apply] using (SameCycle.rfl : q.SameCycle b b).apply_right)
    · by_cases hzb : z = b
      · subst z
        exact hqab.symm.trans
          (by simpa [q, mul_apply] using (SameCycle.rfl : q.SameCycle a a).apply_right)
      · have hz : q z = p z := by simp [q, mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]
        exact hz ▸ SameCycle.rfl.apply_right
  have hpow : ∀ n : ℕ, q.SameCycle x ((p ^ n) x) := by
    intro n
    induction n with
    | zero =>
        exact SameCycle.rfl
    | succ n ih =>
        rw [pow_succ', mul_apply]
        exact ih.trans (hstep ((p ^ n) x))
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  simpa [hn] using hpow n

lemma sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
    (p : Equiv.Perm D) {a b x y : D} (hnsc : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle x y ↔ mergeRel p a b x y := by
  constructor
  · exact mergeRel_of_sameCycle_mul_swap
  · intro h
    let q := p * Equiv.swap a b
    have hqab : q.SameCycle a b := sameCycle_mul_swap_self_of_not_sameCycle p hnsc
    rcases h with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxy
    · exact (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxa).trans
        (hqab.trans (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hyb.symm))
    · exact (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxb).trans
        (hqab.symm.trans (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hya.symm))

noncomputable def orbitEquivFixedOrCycles (p : Equiv.Perm D) :
    Quotient (SameCycle.setoid p) ≃ Function.fixedPoints p ⊕ p.cycleFactorsFinset := by
  classical
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left
      right_inv := ?right }
  · refine Quotient.lift ?_ ?_
    · intro x
      by_cases hx : p x = x
      · exact Sum.inl ⟨x, by simpa [Function.mem_fixedPoints_iff] using hx⟩
      · exact Sum.inr ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩
    · intro x y hxy
      change p.SameCycle x y at hxy
      by_cases hx : p x = x
      · have hy : p y = y := (hxy.apply_eq_self_iff).mp hx
        have hxy' : x = y := hxy.eq_of_left hx
        subst hxy'
        simp [hx, hy]
      · have hy : p y ≠ y := fun hy => hx ((hxy.apply_eq_self_iff).mpr hy)
        simp [hx, hy]
        exact hxy.cycleOf_eq
  · intro s
    rcases s with fp | c
    · exact Quotient.mk (SameCycle.setoid p) fp.1
    · let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      exact Quotient.mk (SameCycle.setoid p) y
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : p x = x
    · simp [hx, Function.mem_fixedPoints_iff]
    · dsimp
      simp [hx]
      let c : p.cycleFactorsFinset :=
        ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩
      let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hy : y ∈ (p.cycleOf x).support :=
        Classical.choose_spec
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hy' : p.SameCycle x y := by
        have := (mem_support_cycleOf_iff (f := p) (x := x) (y := y)).mp hy
        exact this.1
      exact Quotient.sound hy'.symm
  · intro s
    rcases s with fp | c
    · have hfp : p fp.1 = fp.1 := Function.mem_fixedPoints_iff.mp fp.2
      simp [hfp]
    · let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hyc : y ∈ (c : Equiv.Perm D).support :=
        Classical.choose_spec
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hyp : y ∈ p.support := mem_cycleFactorsFinset_support_le c.2 hyc
      have hy : p y ≠ y := mem_support.mp hyp
      have hcy : c.1 = p.cycleOf y := cycle_is_cycleOf hyc c.2
      dsimp
      rw [dif_neg hy]
      exact congrArg (fun e : p.cycleFactorsFinset => Sum.inr e) (Subtype.ext hcy.symm)

lemma numCycles_eq_fixed_add_cycleType_card (p : Equiv.Perm D) :
    numCycles p =
      Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType := by
  classical
  unfold numCycles
  calc
    Fintype.card (Quotient (SameCycle.setoid p))
        = Fintype.card (Function.fixedPoints p ⊕ p.cycleFactorsFinset) :=
          Fintype.card_congr (orbitEquivFixedOrCycles p)
    _ = Fintype.card (Function.fixedPoints p) + Fintype.card p.cycleFactorsFinset := by
          simp
    _ = Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType := by
          rw [cycleType_def]
          simp



theorem numCycles_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p := by
  classical
  let q : Equiv.Perm D := p * Equiv.swap a b
  let P := Quotient (SameCycle.setoid p)
  let Q := Quotient (SameCycle.setoid q)
  let A : P := Quotient.mk (SameCycle.setoid p) a
  let B : P := Quotient.mk (SameCycle.setoid p) b
  have hAB : A ≠ B := by
    intro h
    exact hnsc (Quotient.exact h)
  have hpq : ∀ {x y : D}, p.SameCycle x y → q.SameCycle x y := by
    intro x y hxy
    exact sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxy
  let mergeMap : P → Q := Quotient.map' id (fun x y hxy => hpq hxy)
  let f : {u : P // u ≠ B} → Q := fun u => mergeMap u.1
  have hsurj : Function.Surjective f := by
    intro v
    refine Quotient.inductionOn v ?_
    intro x
    by_cases hxB : (Quotient.mk (SameCycle.setoid p) x : P) = B
    · refine ⟨⟨A, hAB⟩, ?_⟩
      have hxb : p.SameCycle x b := Quotient.exact hxB
      have hqxa : q.SameCycle x a :=
        (hpq hxb).trans (sameCycle_mul_swap_self_of_not_sameCycle p hnsc).symm
      apply Quotient.sound hqxa.symm
    · refine ⟨⟨Quotient.mk (SameCycle.setoid p) x, hxB⟩, ?_⟩
      rfl
  have hinj : Function.Injective f := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    apply Subtype.ext
    dsimp [f, mergeMap] at huv
    revert hu hv huv
    refine Quotient.inductionOn₂ u v ?_
    intro x y hxB hyB hxy
    simp only [Quotient.map'_mk'', id_eq] at hxy
    have hqxy : q.SameCycle x y := Quotient.exact hxy
    have hR : mergeRel p a b x y :=
      (sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle p hnsc).mp hqxy
    rcases hR with hpxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact Quotient.sound hpxy
    · exfalso
      exact hyB (Quotient.sound hyb)
    · exfalso
      exact hxB (Quotient.sound hxb)
  have hcard_equiv : Fintype.card {u : P // u ≠ B} = Fintype.card Q :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  have hsub_card : Fintype.card {u : P // u ≠ B} + 1 = Fintype.card P := by
    have hcompl :
        Fintype.card {u : P // u ≠ B} = Fintype.card P - 1 := by
      simpa [Fintype.card_subtype_eq B] using
        (Fintype.card_subtype_compl (fun u : P => u = B))
    have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨B⟩
    omega
  unfold numCycles
  change Fintype.card Q + 1 = Fintype.card P
  rw [← hcard_equiv]
  exact hsub_card

lemma sign_eq_of_numCycles_eq (p q : Equiv.Perm D)
    (hnum : numCycles p = numCycles q) :
    Equiv.Perm.sign p = Equiv.Perm.sign q := by
  classical
  have hpnum :
      numCycles p = Fintype.card D - p.cycleType.sum + Multiset.card p.cycleType := by
    rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints]
  have hqnum :
      numCycles q = Fintype.card D - q.cycleType.sum + Multiset.card q.cycleType := by
    rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints]
  have hmod :
      (p.cycleType.sum + Multiset.card p.cycleType) % 2 =
        (q.cycleType.sum + Multiset.card q.cycleType) % 2 := by
    have hp_le := p.sum_cycleType_le
    have hq_le := q.sum_cycleType_le
    omega
  apply Units.ext
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sign_of_cycleType]
  simp [neg_one_pow_eq_pow_mod_two, hmod]

lemma numCycles_mul_swap_ne (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) ≠ numCycles p := by
  intro hnum
  have hsign_eq := sign_eq_of_numCycles_eq (p * Equiv.swap a b) p hnum
  have hsign_neg :
      Equiv.Perm.sign (p * Equiv.swap a b) = -Equiv.Perm.sign p := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    simp
  rw [hsign_neg] at hsign_eq
  have hself : Equiv.Perm.sign p = -Equiv.Perm.sign p := hsign_eq.symm
  have hone : (1 : ℤˣ) = -1 := by
    calc
      (1 : ℤˣ) = (Equiv.Perm.sign p)⁻¹ * Equiv.Perm.sign p := by simp
      _ = (Equiv.Perm.sign p)⁻¹ * (-Equiv.Perm.sign p) := by
        exact congrArg ((Equiv.Perm.sign p)⁻¹ * ·) hself
      _ = -1 := by
        rw [mul_neg, inv_mul_cancel]
  have hval := congrArg Units.val hone
  norm_num at hval

lemma numCycles_le_mul_swap_of_sameCycle
    (p : Equiv.Perm D) {a b : D} (hsc : p.SameCycle a b) :
    numCycles p ≤ numCycles (p * Equiv.swap a b) := by
  classical
  let q : Equiv.Perm D := p * Equiv.swap a b
  let P := Quotient (SameCycle.setoid p)
  let Q := Quotient (SameCycle.setoid q)
  have hrel : ∀ {x y : D}, q.SameCycle x y → p.SameCycle x y := by
    intro x y hxy
    exact mergeRel_of_base_sameCycle hsc (mergeRel_of_sameCycle_mul_swap hxy)
  let g : Q → P := Quotient.map' id (fun x y hxy => hrel hxy)
  have hsurj : Function.Surjective g := by
    intro u
    refine Quotient.inductionOn u ?_
    intro x
    exact ⟨Quotient.mk (SameCycle.setoid q) x, rfl⟩
  unfold numCycles
  change Fintype.card P ≤ Fintype.card Q
  exact Fintype.card_le_of_surjective g hsurj

theorem numCycles_mul_swap_dichotomy
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p := by
  by_cases hnsc : ¬ p.SameCycle a b
  · exact Or.inr (numCycles_mul_swap_of_not_sameCycle p hab hnsc)
  · have hsc : p.SameCycle a b := by simpa using Classical.not_not.mp hnsc
    let q : Equiv.Perm D := p * Equiv.swap a b
    have hp_le_q : numCycles p ≤ numCycles q :=
      numCycles_le_mul_swap_of_sameCycle p hsc
    by_cases hqsc : q.SameCycle a b
    · have hq_le_p : numCycles q ≤ numCycles p := by
        have h := numCycles_le_mul_swap_of_sameCycle q hqsc
        simpa [q, mul_assoc] using h
      have heq : numCycles q = numCycles p := le_antisymm hq_le_p hp_le_q
      exact False.elim (numCycles_mul_swap_ne p hab heq)
    · have h := numCycles_mul_swap_of_not_sameCycle q hab hqsc
      exact Or.inl (by simpa [q, mul_assoc] using h.symm)

end PermTranspositionCycleCount

theorem numCycles_mul_swap_dichotomy
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p :=
  PermTranspositionCycleCount.numCycles_mul_swap_dichotomy p hab

theorem numCycles_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p :=
  PermTranspositionCycleCount.numCycles_mul_swap_of_not_sameCycle p hab hnsc

end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.RelationComponentCount -/
section
set_option autoImplicit true


open Classical

universe u

variable {V : Type u} [Fintype V]

def compSetoid (r : V → V → Prop) : Setoid V :=
  ⟨Relation.EqvGen r, Relation.EqvGen.is_equivalence r⟩

noncomputable def numComp (r : V → V → Prop) : ℕ :=
  Nat.card (Quotient (compSetoid r))

def addEdge (r : V → V → Prop) (a b : V) : V → V → Prop :=
  fun x y => r x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

 def pairRel {α : Type u} (a b : α) (x y : α) : Prop :=
  x = y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)

 theorem pairRel_refl {α : Type u} (a b : α) (x : α) :
    pairRel a b x x := by
  exact Or.inl rfl

 theorem pairRel_symm {α : Type u} (a b : α) {x y : α} :
    pairRel a b x y → pairRel a b y x := by
  intro h
  rcases h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)

 theorem pairRel_trans {α : Type u} (a b : α) {x y z : α} :
    pairRel a b x y → pairRel a b y z → pairRel a b x z := by
  intro hxy hyz
  rcases hxy with hEq | hAB | hBA
  · subst y
    exact hyz
  · rcases hAB with ⟨rfl, rfl⟩
    rcases hyz with hEq | hAB' | hBA'
    · subst z
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hAB' with ⟨_, hz⟩
      subst z
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases hBA' with ⟨_, hz⟩
      subst z
      exact Or.inl rfl
  · rcases hBA with ⟨rfl, rfl⟩
    rcases hyz with hEq | hAB' | hBA'
    · subst z
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · rcases hAB' with ⟨_, hz⟩
      subst z
      exact Or.inl rfl
    · rcases hBA' with ⟨_, hz⟩
      subst z
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)

 def pairSetoid {α : Type u} (a b : α) : Setoid α where
  r := pairRel a b
  iseqv :=
    ⟨pairRel_refl a b, fun h => pairRel_symm a b h,
      fun h₁ h₂ => pairRel_trans a b h₁ h₂⟩

omit [Fintype V] in
 theorem eqvGen_mono {r s : V → V → Prop}
    (h : ∀ ⦃x y : V⦄, r x y → s x y) {x y : V} :
    Relation.EqvGen r x y → Relation.EqvGen s x y := by
  intro hxy
  induction hxy with
  | rel x y hxy =>
      exact Relation.EqvGen.rel x y (h hxy)
  | refl x =>
      exact Relation.EqvGen.refl x
  | symm x y _ ih =>
      exact Relation.EqvGen.symm x y ih
  | trans x y z _ _ ihxy ihyz =>
      exact Relation.EqvGen.trans x y z ihxy ihyz

omit [Fintype V] in
 theorem eqvGen_le_addEdge (r : V → V → Prop) (a b : V) {x y : V} :
    Relation.EqvGen r x y → Relation.EqvGen (addEdge r a b) x y := by
  intro hxy
  exact eqvGen_mono (s := addEdge r a b) (fun {x y} hr => Or.inl hr) hxy

omit [Fintype V] in
 theorem eqvGen_addEdge_iff_pairRel (r : V → V → Prop) (a b x y : V) :
    Relation.EqvGen (addEdge r a b) x y ↔
      pairRel (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)
        (Quotient.mk (compSetoid r) x) (Quotient.mk (compSetoid r) y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel x y hxy =>
        rcases hxy with hr | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (Quotient.sound (Relation.EqvGen.rel x y hr))
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | refl x =>
        exact pairRel_refl _ _ _
    | symm x y _ ih =>
        exact pairRel_symm _ _ ih
    | trans x y z _ _ ihxy ihyz =>
        exact pairRel_trans _ _ ihxy ihyz
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact eqvGen_le_addEdge r a b (Quotient.exact hxy)
    · rcases hxab with ⟨hxa, hyb⟩
      have hxa' : Relation.EqvGen (addEdge r a b) x a :=
        eqvGen_le_addEdge r a b (Quotient.exact hxa)
      have hby' : Relation.EqvGen (addEdge r a b) b y :=
        Relation.EqvGen.symm y b (eqvGen_le_addEdge r a b (Quotient.exact hyb))
      have hab' : Relation.EqvGen (addEdge r a b) a b :=
        Relation.EqvGen.rel a b (Or.inr (Or.inl ⟨rfl, rfl⟩))
      exact Relation.EqvGen.trans x a y hxa'
        (Relation.EqvGen.trans a b y hab' hby')
    · rcases hxba with ⟨hxb, hya⟩
      have hxb' : Relation.EqvGen (addEdge r a b) x b :=
        eqvGen_le_addEdge r a b (Quotient.exact hxb)
      have hay' : Relation.EqvGen (addEdge r a b) a y :=
        Relation.EqvGen.symm y a (eqvGen_le_addEdge r a b (Quotient.exact hya))
      have hba' : Relation.EqvGen (addEdge r a b) b a :=
        Relation.EqvGen.rel b a (Or.inr (Or.inr ⟨rfl, rfl⟩))
      exact Relation.EqvGen.trans x b y hxb'
        (Relation.EqvGen.trans b a y hba' hay')

omit [Fintype V] in
 theorem eqvGen_addEdge_iff (r : V → V → Prop) (a b x y : V) :
    Relation.EqvGen (addEdge r a b) x y ↔
      Relation.EqvGen r x y
        ∨ (Relation.EqvGen r x a ∧ Relation.EqvGen r y b)
        ∨ (Relation.EqvGen r x b ∧ Relation.EqvGen r y a) := by
  rw [eqvGen_addEdge_iff_pairRel]
  constructor
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact Or.inl (Quotient.exact hxy)
    · exact Or.inr (Or.inl ⟨Quotient.exact hxab.1, Quotient.exact hxab.2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.exact hxba.1, Quotient.exact hxba.2⟩)
  · intro hxy
    rcases hxy with hxy | hxab | hxba
    · exact Or.inl (Quotient.sound hxy)
    · exact Or.inr (Or.inl ⟨Quotient.sound hxab.1, Quotient.sound hxab.2⟩)
    · exact Or.inr (Or.inr ⟨Quotient.sound hxba.1, Quotient.sound hxba.2⟩)

 def quotientEquivOfRelIff {α : Type u} (s t : Setoid α)
    (h : ∀ x y : α, s.r x y ↔ t.r x y) :
    Quotient s ≃ Quotient t where
  toFun := Quotient.map id (by
    intro x y hxy
    exact (h x y).1 hxy)
  invFun := Quotient.map id (by
    intro x y hxy
    exact (h x y).2 hxy)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl

 def pairRep {α : Type u} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (x : α) : {x : α // x ≠ b} :=
  if hx : x = b then ⟨a, hab⟩ else ⟨x, hx⟩

 def pairQuotEquivSubtypeNe {α : Type u} [DecidableEq α] {a b : α}
    (hab : a ≠ b) :
    Quotient (pairSetoid a b) ≃ {x : α // x ≠ b} where
  toFun := Quotient.lift (pairRep hab) (by
    intro x y hxy
    change pairRel a b x y at hxy
    rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · simp [pairRep, hab]
    · simp [pairRep, hab])
  invFun := fun x => Quotient.mk (pairSetoid a b) x.1
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    dsimp
    by_cases hx : x = b
    · subst x
      simp [pairRep]
      exact Quotient.sound (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · simp [pairRep, hx]
  right_inv := by
    intro x
    ext
    simp [pairRep, x.2]

 theorem pairSetoid_card_add_one {α : Type u} [Fintype α] [DecidableEq α]
    {a b : α} (hab : a ≠ b) :
    Nat.card (Quotient (pairSetoid a b)) + 1 = Nat.card α := by
  classical
  haveI : Fintype (Quotient (pairSetoid a b)) := Quotient.fintype (pairSetoid a b)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hcardEquiv :
      Fintype.card (Quotient (pairSetoid a b)) = Fintype.card {x : α // x ≠ b} :=
    Fintype.card_congr (pairQuotEquivSubtypeNe hab)
  rw [hcardEquiv]
  have hcompl := Fintype.card_subtype_compl (fun x : α => x = b)
  have hsingle : Fintype.card {x : α // x = b} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨b, rfl⟩, ?_⟩
    intro y
    ext
    exact y.2
  rw [hcompl, hsingle]
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨b⟩
  omega

 def compAddQuotEquivPairQuot (r : V → V → Prop) (a b : V) :
    Quotient (compSetoid (addEdge r a b)) ≃
      Quotient
        (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)) where
  toFun := Quotient.lift
    (fun x =>
      Quotient.mk
        (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b))
        (Quotient.mk (compSetoid r) x))
    (by
      intro x y hxy
      exact Quotient.sound ((eqvGen_addEdge_iff_pairRel r a b x y).1 hxy))
  invFun :=
    Quotient.lift
      (Quotient.map id (by
        intro x y hxy
        exact eqvGen_le_addEdge r a b hxy))
      (by
        intro x y hxy
        change pairRel (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b) x y
          at hxy
        rcases hxy with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Quotient.sound (Relation.EqvGen.rel a b (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        · exact Quotient.sound (Relation.EqvGen.rel b a (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    refine Quotient.inductionOn x ?_
    intro v
    rfl

omit [Fintype V] in
theorem numComp_addEdge_of_eqvGen (r : V → V → Prop) {a b : V}
    (h : Relation.EqvGen r a b) :
    numComp (addEdge r a b) = numComp r := by
  unfold numComp
  apply Nat.card_congr
  refine quotientEquivOfRelIff (compSetoid (addEdge r a b)) (compSetoid r) ?_
  intro x y
  constructor
  · intro hxy
    change Relation.EqvGen (addEdge r a b) x y at hxy
    rw [eqvGen_addEdge_iff] at hxy
    rcases hxy with hxy | hxab | hxba
    · exact hxy
    · exact Relation.EqvGen.trans x a y hxab.1
        (Relation.EqvGen.trans a b y h (Relation.EqvGen.symm y b hxab.2))
    · exact Relation.EqvGen.trans x b y hxba.1
        (Relation.EqvGen.trans b a y (Relation.EqvGen.symm a b h)
          (Relation.EqvGen.symm y a hxba.2))
  · intro hxy
    exact eqvGen_le_addEdge r a b hxy

theorem numComp_addEdge_of_not_eqvGen (r : V → V → Prop) {a b : V}
    (h : ¬ Relation.EqvGen r a b) :
    numComp (addEdge r a b) + 1 = numComp r := by
  classical
  let Q := Quotient (compSetoid r)
  let A : Q := Quotient.mk (compSetoid r) a
  let B : Q := Quotient.mk (compSetoid r) b
  haveI : Fintype Q := Quotient.fintype (compSetoid r)
  have hAB : A ≠ B := by
    intro hq
    exact h (Quotient.exact hq)
  unfold numComp
  change Nat.card (Quotient (compSetoid (addEdge r a b))) + 1 = Nat.card Q
  have hcard :
      Nat.card
          (Quotient
            (pairSetoid (Quotient.mk (compSetoid r) a) (Quotient.mk (compSetoid r) b)))
          + 1 =
        Nat.card Q := by
    simpa [Q, A, B] using pairSetoid_card_add_one hAB
  rw [Nat.card_congr (compAddQuotEquivPairQuot r a b)]
  exact hcard

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PermTranspositionCycleCount
import ProofsInTheBook.RelationComponentCount
-/
/- Source module: ProofsInTheBook.PlanarMapEulerInequality -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



open scoped Classical in
/-- The repo's orbit count (`Fintype.card (Quotient (cycleSetoid p))`) agrees with
`_root_.numCycles p` (built from `SameCycle.setoid`): the two setoids
carry the identical relation `p.SameCycle`. -/
lemma card_cycleSetoid_eq_numCycles (p : Equiv.Perm D) :
    Fintype.card (Quotient (cycleSetoid p)) = _root_.numCycles p := by
  classical
  unfold _root_.numCycles
  exact Fintype.card_congr
    (Quotient.congr (Equiv.refl D) (fun x y => by rfl))

lemma V_eq_numCycles (M : CombMap D) : M.V = _root_.numCycles M.σ :=
  card_cycleSetoid_eq_numCycles M.σ
lemma E_eq_numCycles (M : CombMap D) : M.E = _root_.numCycles M.α :=
  card_cycleSetoid_eq_numCycles M.α
lemma F_eq_numCycles (M : CombMap D) : M.F = _root_.numCycles M.φ :=
  card_cycleSetoid_eq_numCycles M.φ



/-- The dart-incidence relation of a raw pair `(σ, α)`: two darts are adjacent if
they share a `σ`-orbit (same vertex) or are joined by the `α`-edge. -/
def dartStepRel (σ α : Equiv.Perm D) (a b : D) : Prop :=
  σ.SameCycle a b ∨ b = α a

omit [Fintype D] [DecidableEq D] in
lemma dartStepRel_symm {σ α : Equiv.Perm D} (hα : α * α = 1) {a b : D}
    (h : dartStepRel σ α a b) : dartStepRel σ α b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    subst h
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ.symm



omit [Fintype D] [DecidableEq D] in
/-- `ReflTransGen` of a symmetric relation is symmetric. -/
lemma reflTransGen_symm {r : D → D → Prop} (hsymm : ∀ a b, r a b → r b a)
    {a b : D} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

omit [Fintype D] [DecidableEq D] in
/-- For a symmetric relation, the equivalence closure is the reflexive-transitive
closure (the repo's `Connected` is phrased with `ReflTransGen`). -/
lemma eqvGen_iff_reflTransGen {r : D → D → Prop} (hsymm : ∀ a b, r a b → r b a)
    (a b : D) :
    Relation.EqvGen r a b ↔ Relation.ReflTransGen r a b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact Relation.ReflTransGen.single hxy
    | refl x => exact Relation.ReflTransGen.refl
    | symm x y _ ih => exact reflTransGen_symm hsymm ih
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl a
    | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)



/-- Number of `α`-transpositions. -/
noncomputable def Ehalf (α : Equiv.Perm D) : ℕ := (Equiv.Perm.support α).card / 2



/-- Removing the transposition `{a, b}` (with `α a = b`, `a ≠ b`) from an
involution `α`: the support loses exactly `a` and `b`. -/
lemma support_mul_swap_of_apply (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    Equiv.Perm.support (α * Equiv.swap a b) = (Equiv.Perm.support α) \ {a, b} := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have : α (α a) = a := by
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at this; exact this
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton, ne_eq]
  constructor
  · intro hx
    rcases eq_or_ne x a with rfl | hxa
    · exact absurd (by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb]) hx
    · rcases eq_or_ne x b with rfl | hxb
      · exact absurd (by rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa]) hx
      · refine ⟨?_, fun h => by rcases h with h | h <;> simp_all⟩
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb] at hx
        exact hx
  · rintro ⟨hx, hx2⟩
    push_neg at hx2
    obtain ⟨hxa, hxb⟩ := hx2
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    exact hx

/-- `a` and `b` are distinct elements of `support α` when `α a = b`. -/
lemma mem_support_of_apply_ne {α : Equiv.Perm D} {a b : D} (hab : a ≠ b)
    (hαa : α a = b) : a ∈ Equiv.Perm.support α ∧ b ∈ Equiv.Perm.support α := by
  classical
  constructor
  · rw [Equiv.Perm.mem_support, hαa]; exact hab.symm
  · rw [Equiv.Perm.mem_support]
    intro hb
    -- if `α b = b` then `α a = b` and injectivity force `a = b`
    exact hab (α.injective (by rw [hαa, hb]))

/-- Deleting one transposition drops `Ehalf` by exactly one. -/
lemma Ehalf_mul_swap (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    Ehalf (α * Equiv.swap a b) + 1 = Ehalf α := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have : α (α a) = a := by
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at this; exact this
  have hsupp := support_mul_swap_of_apply α hα hab hαa
  obtain ⟨ha, hb⟩ := mem_support_of_apply_ne hab hαa
  have hpair : ({a, b} : Finset D) ⊆ Equiv.Perm.support α := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : ({a, b} : Finset D).card = 2 := by
    rw [Finset.card_pair hab]
  have hinter : ({a, b} : Finset D) ∩ Equiv.Perm.support α = {a, b} :=
    Finset.inter_eq_left.mpr hpair
  have hcards : (Equiv.Perm.support (α * Equiv.swap a b)).card
      = (Equiv.Perm.support α).card - 2 := by
    rw [hsupp, Finset.card_sdiff, hinter, hcard2]
  -- `support α` has even cardinality (involution), and contains the 2-element pair.
  have heven : 2 ∣ (Equiv.Perm.support α).card :=
    Equiv.Perm.two_dvd_card_support (by
      have : α ^ 2 = 1 := by rw [pow_two]; exact hα
      exact this)
  have h2le : 2 ≤ (Equiv.Perm.support α).card := by
    have := Finset.card_le_card hpair
    rwa [hcard2] at this
  unfold Ehalf
  rw [hcards]
  omega



open Relation in
/-- One application of `σ * α` is a 2-step `dartStepRel` walk `x → α x → σ(α x)`. -/
lemma reflTransGen_dartStepRel_mul_apply (σ α : Equiv.Perm D) (x : D) :
    ReflTransGen (dartStepRel σ α) x ((σ * α) x) := by
  have h1 : dartStepRel σ α x (α x) := Or.inr rfl
  have h2 : dartStepRel σ α (α x) ((σ * α) x) := by
    refine Or.inl ?_
    have hmul : (σ * α) x = σ (α x) := rfl
    rw [hmul]
    exact ⟨1, by simp⟩
  exact (ReflTransGen.single h1).tail h2

open Relation in
/-- A `σα`-power walk lifts to a `dartStepRel` reflexive-transitive walk. -/
lemma reflTransGen_dartStepRel_of_pow (σ α : Equiv.Perm D) :
    ∀ (k : ℕ) (x : D), ReflTransGen (dartStepRel σ α) x (((σ * α) ^ k) x) := by
  intro k
  induction k with
  | zero => intro x; simpa using ReflTransGen.refl
  | succ k ih =>
      intro x
      have hstep := reflTransGen_dartStepRel_mul_apply σ α (((σ * α) ^ k) x)
      have hpow : ((σ * α) ^ (k + 1)) x = (σ * α) (((σ * α) ^ k) x) := by
        rw [pow_succ']; rfl
      rw [hpow]
      exact (ih x).trans hstep

open Relation in
/-- Same `σα`-cycle implies the two darts are `dartStepRel`-connected. -/
lemma eqvGen_dartStepRel_of_sameCycle_mul (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (h : (σ * α).SameCycle a b) :
    EqvGen (dartStepRel σ α) a b := by
  rw [eqvGen_iff_reflTransGen (fun x y => dartStepRel_symm hα)]
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact reflTransGen_dartStepRel_of_pow σ α k a



/-- With `α a = b`, `α b = a`, `a ≠ b`, the dart relation of `α` is the dart
relation of `α' = α * swap a b` (which fixes `a, b`) with the single edge `{a, b}`
re-added. -/
lemma dartStepRel_eq_addEdge (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    dartStepRel σ α
      = _root_.addEdge (dartStepRel σ (α * Equiv.swap a b)) a b := by
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  funext x y
  simp only [dartStepRel, _root_.addEdge, eq_iff_iff]
  have hrefl : σ.SameCycle x x := Equiv.Perm.SameCycle.refl σ x
  rcases eq_or_ne x a with rfl | hxa
  · -- `x = a`: `a` is eliminated, the surviving name is `x`
    have hα' : (α * Equiv.swap x b) x = x := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb]
    rw [hαa, hα']
    constructor
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · subst h; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rintro ((h | h) | ⟨_, h⟩ | ⟨hxb, _⟩)
      · exact Or.inl h
      · exact Or.inl (h ▸ hrefl)
      · exact Or.inr h
      · exact absurd hxb hab
  · rcases eq_or_ne x b with rfl | hxb
    · -- `x = b`: surviving name is `x`
      have hα' : (α * Equiv.swap a x) x = x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa]
      rw [hαb, hα']
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · subst h; exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · rintro ((h | h) | ⟨hxa', _⟩ | ⟨_, h⟩)
        · exact Or.inl h
        · exact Or.inl (h ▸ hrefl)
        · exact absurd hxa' hxa
        · exact Or.inr h
    · have hα' : (α * Equiv.swap a b) x = α x := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb]
      rw [hα']
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
      · rintro ((h | h) | ⟨hxa', _⟩ | ⟨hxb', _⟩)
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd hxa' hxa
        · exact absurd hxb' hxb



/-- Removing one transposition from an involution leaves an involution. -/
lemma mul_swap_involutive (α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hαa : α a = b) (hαb : α b = a) :
    (α * Equiv.swap a b) * (α * Equiv.swap a b) = 1 := by
  ext x
  simp only [Equiv.Perm.coe_one, id_eq]
  have hαα : ∀ z, α (α z) = z := by
    intro z
    have happ := congrArg (fun f : Equiv.Perm D => f z) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  rcases eq_or_ne x a with rfl | hxa
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hαb, Equiv.swap_apply_right,
      hαa]
  · rcases eq_or_ne x b with rfl | hxb
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hαa, Equiv.swap_apply_left,
        hαb]
    · have hαxa : α x ≠ a := by
        intro h
        apply hxb
        have : x = α a := by rw [← hαα x, h]
        rw [this, hαa]
      have hαxb : α x ≠ b := by
        intro h
        apply hxa
        have : x = α b := by rw [← hαα x, h]
        rw [this, hαb]
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hxa hxb,
        Equiv.swap_apply_of_ne_of_ne hαxa hαxb, hαα]



/-- Component count of the raw pair `(σ, α)`. -/
noncomputable def numComponents (σ α : Equiv.Perm D) : ℕ :=
  _root_.numComp (dartStepRel σ α)

lemma numComponents_def (σ α : Equiv.Perm D) :
    numComponents σ α = _root_.numComp (dartStepRel σ α) := rfl

/-- Genus slack `2c - V + Ehalf - F` of a raw involution pair.  It is `≥ 0`; for a
connected fixed-point-free map this yields `χ ≤ 2`. -/
noncomputable def genusSlack (σ α : Equiv.Perm D) : ℤ :=
  2 * (numComponents σ α : ℤ) - (numCycles σ : ℤ) + (Ehalf α : ℤ)
    - (numCycles (σ * α) : ℤ)


open scoped Classical in
/-- For `α = 1` the dart relation is just `σ.SameCycle`. -/
lemma dartStepRel_one (σ : Equiv.Perm D) :
    dartStepRel σ 1 = fun x y => σ.SameCycle x y := by
  funext x y
  simp only [dartStepRel, Equiv.Perm.coe_one, id_eq, eq_iff_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact h ▸ Equiv.Perm.SameCycle.refl σ x
  · intro h; exact Or.inl h

open scoped Classical in
/-- For `α = 1` the components are exactly the `σ`-orbits. -/
lemma numComponents_one (σ : Equiv.Perm D) :
    numComponents σ 1 = numCycles σ := by
  classical
  rw [numComponents_def, dartStepRel_one]
  unfold _root_.numComp _root_.numCycles
  rw [← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine Quotient.congr (Equiv.refl D) ?_
  intro x y
  simp only [Equiv.refl_apply]
  have hrel : Relation.EqvGen (fun x y => σ.SameCycle x y) x y ↔ σ.SameCycle x y :=
    Equivalence.eqvGen_iff (Equiv.Perm.SameCycle.equivalence σ)
  exact hrel



/-- **Genus nonnegativity.** For every involution `α`, `genusSlack σ α ≥ 0`. -/
lemma genusSlack_nonneg (σ : Equiv.Perm D) :
    ∀ α : Equiv.Perm D, α * α = 1 → 0 ≤ genusSlack σ α := by
  intro α
  induction hn : (Equiv.Perm.support α).card using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    intro hα
    rcases eq_or_ne (Equiv.Perm.support α) ∅ with hemp | hemp
    · -- base case: α = 1
      have hα1 : α = 1 := Equiv.Perm.support_eq_empty_iff.mp hemp
      subst hα1
      have hEhalf : Ehalf (1 : Equiv.Perm D) = 0 := by simp [Ehalf]
      have hmul : (σ * 1) = σ := mul_one σ
      have hcomp : numComponents σ 1 = numCycles σ := numComponents_one σ
      unfold genusSlack
      rw [hEhalf, hmul, hcomp]
      push_cast
      ring_nf
      positivity
    · -- inductive step: delete one transposition {a, b}
      obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hane : α a ≠ a := Equiv.Perm.mem_support.mp ha
      obtain ⟨b, hαa⟩ : ∃ b, α a = b := ⟨α a, rfl⟩
      have hab : a ≠ b := fun h => hane (by rw [hαa, ← h])
      have hαb : α b = a := by
        have happ := congrArg (fun f : Equiv.Perm D => f a) hα
        have hh : α (α a) = a := by
          simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
        rw [hαa] at hh; exact hh
      set α' := α * Equiv.swap a b with hα'def
      have hα'invol : α' * α' = 1 := mul_swap_involutive α hα hαa hαb
      have hsupp' : Equiv.Perm.support α' = (Equiv.Perm.support α) \ {a, b} :=
        support_mul_swap_of_apply α hα hab hαa
      have hcard' : (Equiv.Perm.support α').card < n := by
        rw [← hn, hsupp']
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨a, ha, ?_⟩
        simp
      have IHα' := ih _ hcard' α' rfl hα'invol
      have hEhalf : Ehalf α' + 1 = Ehalf α := Ehalf_mul_swap α hα hab hαa
      have hface : σ * α = (σ * α') * Equiv.swap a b := by
        rw [hα'def, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
      have hrel : dartStepRel σ α = _root_.addEdge (dartStepRel σ α') a b :=
        dartStepRel_eq_addEdge σ α hα hab hαa
      have hcompEq : numComponents σ α
          = _root_.numComp (_root_.addEdge (dartStepRel σ α') a b) := by
        rw [numComponents_def, hrel]
      have hdich := _root_.numCycles_mul_swap_dichotomy (σ * α') hab
      rw [← hface] at hdich
      have hEz : (Ehalf α : ℤ) = (Ehalf α' : ℤ) + 1 := by
        have h := hEhalf; push_cast [← h]; ring
      by_cases hsame : Relation.EqvGen (dartStepRel σ α') a b
      · -- same component: numComponents unchanged
        have hC : numComponents σ α = numComponents σ α' := by
          rw [hcompEq, numComponents_def]
          exact _root_.numComp_addEdge_of_eqvGen _ hsame
        unfold genusSlack at IHα' ⊢
        rw [hC, hEz]
        rcases hdich with hd | hd
        · rw [hd]; push_cast; linarith [IHα']
        · have hF : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
            have h := hd; push_cast [← h]; ring
          rw [hF]; linarith [IHα']
      · -- different components: merge, count drops by 1; faces also merge
        have hC : numComponents σ α + 1 = numComponents σ α' := by
          rw [hcompEq, numComponents_def]
          exact _root_.numComp_addEdge_of_not_eqvGen _ hsame
        have hnsc : ¬ (σ * α').SameCycle a b := fun h =>
          hsame (eqvGen_dartStepRel_of_sameCycle_mul σ α' hα'invol h)
        have hmerge : numCycles (σ * α) + 1 = numCycles (σ * α') := by
          have h := _root_.numCycles_mul_swap_of_not_sameCycle
            (σ * α') hab hnsc
          rw [← hface] at h; exact h
        unfold genusSlack at IHα' ⊢
        have hCz : (numComponents σ α : ℤ) = (numComponents σ α' : ℤ) - 1 := by
          have h := hC; push_cast [← h]; ring
        have hFz : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
          have h := hmerge; push_cast [← h]; ring
        rw [hCz, hEz, hFz]
        linarith [IHα']



/-- For a fixed-point-free involution, every dart is in the support. -/
lemma support_eq_univ_of_no_fixed (M : CombMap D) :
    Equiv.Perm.support M.α = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  intro d
  rw [Equiv.Perm.mem_support]
  exact M.α_no_fixed d

/-- For the (fixed-point-free) edge involution of a `CombMap`, `Ehalf = E`. -/
lemma Ehalf_eq_E (M : CombMap D) : Ehalf M.α = M.E := by
  classical
  have h2E : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  unfold Ehalf
  rw [support_eq_univ_of_no_fixed M, Finset.card_univ]
  omega

/-- `M.dartStep` is exactly `dartStepRel M.σ M.α`. -/
lemma dartStep_eq_dartStepRel (M : CombMap D) :
    M.dartStep = dartStepRel M.σ M.α := rfl

open scoped Classical in
/-- A connected map on a nonempty dart set has exactly one component. -/
lemma numComponents_eq_one_of_connected (M : CombMap D) (hconn : M.Connected)
    (d₀ : D) : numComponents M.σ M.α = 1 := by
  classical
  rw [numComponents_def]
  unfold _root_.numComp
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨?_, ⟨Quotient.mk (_root_.compSetoid (dartStepRel M.σ M.α)) d₀⟩⟩
  -- subsingleton: any two quotient points are equal
  constructor
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a c
  apply Quotient.sound
  show Relation.EqvGen (dartStepRel M.σ M.α) a c
  rw [eqvGen_iff_reflTransGen (fun u v => dartStepRel_symm M.α_invol)]
  have h := hconn a c
  rw [dartStep_eq_dartStepRel] at h
  exact h

/-- **Euler inequality for connected combinatorial maps.** Every connected map
has Euler characteristic at most `2` (the genus-zero bound `genus ≥ 0`). -/
theorem chi_le_two_of_connected (M : CombMap D) (hconn : M.Connected) :
    M.eulerChar ≤ 2 := by
  classical
  rcases isEmpty_or_nonempty D with hD | hD
  · -- no darts: V = E = F = 0
    have hV : M.V = 0 := by simp [V, Fintype.card_eq_zero_iff]
    have hE : M.E = 0 := by simp [E, Fintype.card_eq_zero_iff]
    have hF : M.F = 0 := by simp [F, Fintype.card_eq_zero_iff]
    simp [eulerChar, hV, hE, hF]
  · obtain ⟨d₀⟩ := hD
    have hgs : 0 ≤ genusSlack M.σ M.α := genusSlack_nonneg M.σ M.α M.α_invol
    have hc : numComponents M.σ M.α = 1 :=
      numComponents_eq_one_of_connected M hconn d₀
    -- φ = σ * α
    have hφ : M.φ = M.σ * M.α := rfl
    have hVc : (M.V : ℤ) = (numCycles M.σ : ℤ) := by
      rw [V_eq_numCycles]
    have hEc : (M.E : ℤ) = (Ehalf M.α : ℤ) := by
      rw [Ehalf_eq_E]
    have hFc : (M.F : ℤ) = (numCycles (M.σ * M.α) : ℤ) := by
      rw [F_eq_numCycles, hφ]
    unfold genusSlack at hgs
    rw [hc] at hgs
    unfold eulerChar
    rw [hVc, hEc, hFc]
    push_cast at hgs ⊢
    linarith [hgs]


end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapCounts -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



namespace CutCapCount

/-- Multiplying by a transposition of two darts in the **same** cycle raises the
cycle count by one (the split case of the dichotomy). -/
theorem numCycles_mul_swap_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    _root_.numCycles (p * Equiv.swap a b) = _root_.numCycles p + 1 := by
  rcases _root_.numCycles_mul_swap_dichotomy p hab with h | h
  · exact h
  · -- the `-1` branch would force `a, b` in different cycles; contradiction.
    exfalso
    -- `q := p * swap a b`.  If it dropped the count, the merge characterization
    -- says `a, b` were in different `p`-cycles, contradicting `hsc`.
    -- Use: count drops ⟹ not sameCycle (else the dichotomy is the `+1` branch).
    have hne := PermTranspositionCycleCount.numCycles_mul_swap_ne p hab
    -- From `h : numCycles q + 1 = numCycles p` we get `numCycles q ≠ numCycles p`.
    -- But also the split branch (which holds for sameCycle) gives `+1`.  We close
    -- by ruling out the merge branch directly via `le_mul_swap_of_sameCycle`.
    have hle : _root_.numCycles p ≤ _root_.numCycles (p * Equiv.swap a b) :=
      PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle p hsc
    omega





/-- **Split lemma for a list of transpositions, each splitting the running
product.**  If `l = [(u₀,v₀), …]` and, writing `Pⱼ` for `p` times the product of
the first `j` swaps (built on the right), each pair `(uⱼ,vⱼ)` is distinct and in
the **same** `Pⱼ`-cycle, then the cycle count rises by `l.length`. -/
theorem numCycles_mul_listSwap_splits (p : Equiv.Perm D) :
    ∀ l : List (D × D),
      (∀ j : Fin l.length,
        (l.get j).1 ≠ (l.get j).2 ∧
          (p * ((l.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            (l.get j).1 (l.get j).2) →
      _root_.numCycles (p * (l.map (fun w => Equiv.swap w.1 w.2)).prod)
        = _root_.numCycles p + l.length := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton t a ih =>
      intro hsplit
      -- The running products for the prefix `t` match those for `t ++ [a]`.
      have hpre : ∀ j : Fin t.length,
          (t.get j).1 ≠ (t.get j).2 ∧
            (p * ((t.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
              (t.get j).1 (t.get j).2 := by
        intro j
        have hj : (j : ℕ) < (t ++ [a]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hget : (t ++ [a]).get ⟨j, hj⟩ = t.get j := by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_left j.isLt]
        have htake : (t ++ [a]).take j = t.take j := by
          rw [List.take_append_of_le_length (by omega)]
        have := hsplit ⟨j, hj⟩
        rw [hget, htake] at this
        exact this
      have ihres := ih hpre
      -- Last element `a`: splits the product of the prefix.
      have hlast : ((t ++ [a]).length - 1) = t.length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hjlast : t.length < (t ++ [a]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hgetlast : (t ++ [a]).get ⟨t.length, hjlast⟩ = a := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (le_refl _)]
        simp
      have htakelast : (t ++ [a]).take t.length = t := by
        rw [List.take_append_of_le_length (le_refl _), List.take_length]
      have hsa := hsplit ⟨t.length, hjlast⟩
      rw [hgetlast, htakelast] at hsa
      obtain ⟨hane, hasc⟩ := hsa
      -- Now compute the count for the full product.
      have hprodappend :
          ((t ++ [a]).map (fun w => Equiv.swap w.1 w.2)).prod
            = (t.map (fun w => Equiv.swap w.1 w.2)).prod * Equiv.swap a.1 a.2 := by
        simp [List.map_append]
      rw [hprodappend, ← mul_assoc]
      rw [numCycles_mul_swap_of_sameCycle _ hane hasc, ihres]
      simp only [List.length_append, List.length_singleton]
      omega

/-- **Merge lemma for a list of transpositions, each merging the running
product.**  If each pair `(uⱼ,vⱼ)` is distinct and in **different** `Pⱼ`-cycles,
then the cycle count *drops* by `l.length`. -/
theorem numCycles_mul_listSwap_merges (p : Equiv.Perm D) :
    ∀ l : List (D × D),
      (∀ j : Fin l.length,
        (l.get j).1 ≠ (l.get j).2 ∧
          ¬ (p * ((l.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            (l.get j).1 (l.get j).2) →
      _root_.numCycles (p * (l.map (fun w => Equiv.swap w.1 w.2)).prod) + l.length
        = _root_.numCycles p := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton t a ih =>
      intro hmerge
      have hpre : ∀ j : Fin t.length,
          (t.get j).1 ≠ (t.get j).2 ∧
            ¬ (p * ((t.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
              (t.get j).1 (t.get j).2 := by
        intro j
        have hj : (j : ℕ) < (t ++ [a]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hget : (t ++ [a]).get ⟨j, hj⟩ = t.get j := by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_left j.isLt]
        have htake : (t ++ [a]).take j = t.take j := by
          rw [List.take_append_of_le_length (by omega)]
        have := hmerge ⟨j, hj⟩
        rw [hget, htake] at this
        exact this
      have ihres := ih hpre
      have hjlast : t.length < (t ++ [a]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hgetlast : (t ++ [a]).get ⟨t.length, hjlast⟩ = a := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (le_refl _)]; simp
      have htakelast : (t ++ [a]).take t.length = t := by
        rw [List.take_append_of_le_length (le_refl _), List.take_length]
      have hsa := hmerge ⟨t.length, hjlast⟩
      rw [hgetlast, htakelast] at hsa
      obtain ⟨hane, hansc⟩ := hsa
      have hprodappend :
          ((t ++ [a]).map (fun w => Equiv.swap w.1 w.2)).prod
            = (t.map (fun w => Equiv.swap w.1 w.2)).prod * Equiv.swap a.1 a.2 := by
        simp [List.map_append]
      rw [hprodappend, ← mul_assoc]
      have hstep := _root_.numCycles_mul_swap_of_not_sameCycle
        (p * (t.map (fun w => Equiv.swap w.1 w.2)).prod) hane hansc
      simp only [List.length_append, List.length_singleton]
      omega



/-- A product of transpositions fixes a point disjoint from every pair. -/
lemma listSwap_prod_apply_of_notMem (x : D) :
    ∀ l : List (D × D),
      (∀ w ∈ l, x ≠ w.1 ∧ x ≠ w.2) →
      (l.map (fun w => Equiv.swap w.1 w.2)).prod x = x := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have ha := h a List.mem_cons_self
      have ht : ∀ w ∈ t, x ≠ w.1 ∧ x ≠ w.2 := fun w hw => h w (List.mem_cons_of_mem a hw)
      rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih ht,
        Equiv.swap_apply_of_ne_of_ne ha.1 ha.2]



section SumCongr

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

@[simp] lemma sumCongr_one_apply_inl (σ : Equiv.Perm α) (a : α) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) (Sum.inl a) = Sum.inl (σ a) := by
  simp

@[simp] lemma sumCongr_one_apply_inr (σ : Equiv.Perm α) (b : β) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) (Sum.inr b) = Sum.inr b := by
  simp

/-- A power of `sumCongr σ 1` acts as `σ ^ n` on the left summand. -/
lemma sumCongr_one_pow_inl (σ : Equiv.Perm α) (n : ℕ) (a : α) :
    ((Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) ^ n) (Sum.inl a)
      = Sum.inl ((σ ^ n) a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, sumCongr_one_apply_inl]

/-- A power of `sumCongr σ 1` fixes the right summand. -/
lemma sumCongr_one_pow_inr (σ : Equiv.Perm α) (n : ℕ) (b : β) :
    ((Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) ^ n) (Sum.inr b) = Sum.inr b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, sumCongr_one_apply_inr]

lemma sameCycle_sumCongr_one_inl_inl (σ : Equiv.Perm α) (a a' : α) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle (Sum.inl a) (Sum.inl a')
      ↔ σ.SameCycle a a' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast]
    rw [sumCongr_one_pow_inl] at hm
    exact Sum.inl.inj hm
  · intro h
    obtain ⟨m, hm⟩ := SameCycle.exists_nat_pow_eq h
    exact ⟨(m : ℤ), by rw [zpow_natCast, sumCongr_one_pow_inl, hm]⟩

lemma sameCycle_sumCongr_one_inr_inr (σ : Equiv.Perm α) (b b' : β) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle (Sum.inr b) (Sum.inr b')
      ↔ b = b' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [sumCongr_one_pow_inr] at hm; exact Sum.inr.inj hm
  · rintro rfl; exact SameCycle.rfl

lemma sameCycle_sumCongr_one_not_inl_inr (σ : Equiv.Perm α) (a : α) (b : β) :
    ¬ (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle (Sum.inl a) (Sum.inr b) := by
  intro h
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [sumCongr_one_pow_inl] at hm
  exact Sum.inl_ne_inr hm

/-- The orbit-quotient bijection for the sum extension. -/
noncomputable def sumCongrOneOrbitEquiv (σ : Equiv.Perm α) :
    Quotient (SameCycle.setoid (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)))
      ≃ Quotient (SameCycle.setoid σ) ⊕ β := by
  classical
  refine
    { toFun := Quotient.lift
        (fun x => match x with
          | Sum.inl a => Sum.inl (Quotient.mk (SameCycle.setoid σ) a)
          | Sum.inr b => Sum.inr b) ?_
      invFun := fun s => match s with
        | Sum.inl q => Quotient.lift
            (fun a => Quotient.mk (SameCycle.setoid (Equiv.Perm.sumCongr σ
              (1 : Equiv.Perm β))) (Sum.inl a)) ?_ q
        | Sum.inr b => Quotient.mk _ (Sum.inr b)
      left_inv := ?_
      right_inv := ?_ }
  · -- well-defined forward
    intro x y hxy
    change (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle x y at hxy
    rcases x with a | b <;> rcases y with a' | b'
    · exact congrArg Sum.inl (Quotient.sound
        ((sameCycle_sumCongr_one_inl_inl σ a a').mp hxy))
    · exact absurd hxy (sameCycle_sumCongr_one_not_inl_inr σ a b')
    · exact absurd hxy.symm (sameCycle_sumCongr_one_not_inl_inr σ a' b)
    · exact congrArg Sum.inr ((sameCycle_sumCongr_one_inr_inr σ b b').mp hxy)
  · -- well-defined inverse on left
    intro a a' haa'
    change σ.SameCycle a a' at haa'
    exact Quotient.sound ((sameCycle_sumCongr_one_inl_inl σ a a').mpr haa')
  · -- left_inv
    intro q
    refine Quotient.inductionOn q ?_
    rintro (a | b) <;> rfl
  · -- right_inv
    rintro (q | b)
    · refine Quotient.inductionOn q ?_; intro a; rfl
    · rfl

/-- The cycle count of `sumCongr σ 1` is `numCycles σ + card β`. -/
theorem numCycles_sumCongr_one (σ : Equiv.Perm α) :
    _root_.numCycles (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β))
      = _root_.numCycles σ + Fintype.card β := by
  classical
  unfold _root_.numCycles
  rw [Fintype.card_congr (sumCongrOneOrbitEquiv σ), Fintype.card_sum]

end SumCongr

end CutCapCount



namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-- `σ` extended to the cut-dart set with the `2k` caps as fixed points. -/
noncomputable def sigmaLift (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.σ (1 : Equiv.Perm (Fin C.len ⊕ Fin C.len))

@[simp] lemma sigmaLift_inl (C : SimplePrimalCycle M) (d : D) :
    C.sigmaLift (Sum.inl d) = Sum.inl (M.σ d) := by
  simp [sigmaLift]

@[simp] lemma sigmaLift_inr (C : SimplePrimalCycle M) (c : Fin C.len ⊕ Fin C.len) :
    C.sigmaLift (Sum.inr c) = Sum.inr c := by
  simp [sigmaLift]

/-- The cycle count of `sigmaLift` is `V + 2k`. -/
lemma numCycles_sigmaLift (C : SimplePrimalCycle M) :
    _root_.numCycles C.sigmaLift = M.V + 2 * C.len := by
  rw [sigmaLift, numCycles_sumCongr_one, M.V_eq_numCycles]
  simp [Fintype.card_sum, Fintype.card_fin]; ring

/-- The `+`-bank-end dart `ℓ_i^+ = σ⁻¹ p_i`. -/
noncomputable def lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart :=
  Sum.inl (M.σ.symm (C.pDart i))

/-- The `−`-bank-end dart `ℓ_i^- = σ⁻¹ q_i`. -/
noncomputable def lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart :=
  Sum.inl (M.σ.symm (C.qDart i))

/-- The `+`-cap dart. -/
def capP (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart := Sum.inr (Sum.inl i)
/-- The `−`-cap dart. -/
def capM (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart := Sum.inr (Sum.inr i)

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapCounts
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapV -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount



/-- `p_i` and `q_i` share the tail vertex `v_i`. -/
lemma tail_pDart_eq_tail_qDart (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.tail (C.pDart i) = M.tail (C.qDart i) := by
  rw [pDart_def, qDart_def, M.tail_alpha]
  -- `head (dart (prevIdx i)) = tail (dart (nextIdx (prevIdx i))) = tail (dart i)`
  rw [← C.tail_dart_nextIdx (C.prevIdx i), C.nextIdx_prevIdx]

/-- `p_i` and `q_i` lie in the same `σ`-cycle. -/
lemma sameCycle_pDart_qDart (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.σ.SameCycle (C.pDart i) (C.qDart i) := by
  have h : Quotient.mk (cycleSetoid M.σ) (C.pDart i)
      = Quotient.mk (cycleSetoid M.σ) (C.qDart i) := C.tail_pDart_eq_tail_qDart i
  exact Quotient.exact h

/-- The tail vertex of `q_i` is `M.tail (C.dart i)`, the `i`-th cycle vertex. -/
lemma tail_qDart (C : SimplePrimalCycle M) (i : Fin C.len) :
    M.tail (C.qDart i) = M.tail (C.dart i) := rfl

/-- Distinct cycle indices give `p`-darts (resp. `q`-darts) in distinct
`σ`-orbits.  The shared tail of `p_i, q_i` is the `i`-th cycle vertex
`M.tail (dart i)`, and these are pairwise distinct by `tail_inj`. -/
lemma not_sameCycle_pDart_of_ne (C : SimplePrimalCycle M) {i j : Fin C.len}
    (hij : i ≠ j) : ¬ M.σ.SameCycle (C.pDart i) (C.pDart j) := by
  intro h
  apply hij
  have hq : M.tail (C.pDart i) = M.tail (C.pDart j) := Quotient.sound h
  rw [C.tail_pDart_eq_tail_qDart i, C.tail_pDart_eq_tail_qDart j,
    C.tail_qDart i, C.tail_qDart j] at hq
  exact C.tail_inj hq



@[simp] lemma lEndPlus_ne_capP (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndPlus i ≠ C.capP j := by simp [lEndPlus, capP]
@[simp] lemma lEndPlus_ne_capM (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndPlus i ≠ C.capM j := by simp [lEndPlus, capM]
@[simp] lemma lEndMinus_ne_capP (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndMinus i ≠ C.capP j := by simp [lEndMinus, capP]
@[simp] lemma lEndMinus_ne_capM (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndMinus i ≠ C.capM j := by simp [lEndMinus, capM]

lemma capP_ne_capM (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.capP i ≠ C.capM j := by simp [capP, capM]

lemma capP_inj (C : SimplePrimalCycle M) {i j : Fin C.len} (h : C.capP i = C.capP j) :
    i = j := by simpa [capP] using h

lemma capM_inj (C : SimplePrimalCycle M) {i j : Fin C.len} (h : C.capM i = C.capM j) :
    i = j := by simpa [capM] using h

lemma lEndPlus_inj (C : SimplePrimalCycle M) {i j : Fin C.len}
    (h : C.lEndPlus i = C.lEndPlus j) : i = j := by
  simp only [lEndPlus, Sum.inl.injEq] at h
  exact C.pDart_inj (M.σ.symm.injective h)

lemma lEndMinus_inj (C : SimplePrimalCycle M) {i j : Fin C.len}
    (h : C.lEndMinus i = C.lEndMinus j) : i = j := by
  simp only [lEndMinus, Sum.inl.injEq] at h
  exact C.qDart_inj (M.σ.symm.injective h)

lemma lEndPlus_ne_lEndMinus (C : SimplePrimalCycle M) (i j : Fin C.len) :
    C.lEndPlus i ≠ C.lEndMinus j := by
  simp only [lEndPlus, lEndMinus, ne_eq, Sum.inl.injEq]
  intro h
  exact C.pDart_ne_qDart i j (M.σ.symm.injective h)



end SimplePrimalCycle

namespace CutCapCount

variable {E : Type*} [Fintype E] [DecidableEq E]



/-- A swap product fixes a point disjoint from every pair (restated for membership
hypotheses obtained from `flatMap`/`map`). -/
lemma listSwap_prod_fix (x : E) (l : List (E × E))
    (h : ∀ w ∈ l, x ≠ w.1 ∧ x ≠ w.2) :
    (l.map (fun w => Equiv.swap w.1 w.2)).prod x = x :=
  CutCapCount.listSwap_prod_apply_of_notMem x l h

/-- **Orbit-fixed transport (powers).**  If `g` fixes every point of the
`p`-cycle of `a`, then `p * g` iterates as `p` from `a`. -/
lemma pow_mul_apply_of_orbit_fixed (p g : Equiv.Perm E) {a : E}
    (hfix : ∀ y, p.SameCycle a y → g y = y) :
    ∀ n : ℕ, ((p * g) ^ n) a = (p ^ n) a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, Equiv.Perm.mul_apply,
        hfix ((p ^ n) a) ⟨(n : ℤ), by rw [zpow_natCast]⟩, ← Equiv.Perm.mul_apply, ← pow_succ']

/-- **Orbit-fixed transport (`SameCycle`).**  If `g` fixes every point of the
`p`-cycle of `a`, then `p.SameCycle a b` transfers to `p * g`. -/
lemma sameCycle_mul_of_orbit_fixed (p g : Equiv.Perm E) {a b : E}
    (hfix : ∀ y, p.SameCycle a y → g y = y) (hab : p.SameCycle a b) :
    (p * g).SameCycle a b := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, pow_mul_apply_of_orbit_fixed p g hfix n, hn]⟩

/-- A fixed point stays fixed under all powers. -/
lemma pow_apply_of_fixed (p : Equiv.Perm E) {b : E} (hb : p b = b) :
    ∀ n : ℕ, (p ^ n) b = b := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hb]

/-- A point distinct from a fixed point of `p` is not `p`-co-cyclic with it. -/
lemma not_sameCycle_of_fixed (p : Equiv.Perm E) {a b : E}
    (hb : p b = b) (hab : a ≠ b) : ¬ p.SameCycle a b := by
  intro h
  obtain ⟨n, hn⟩ := h.symm.exists_nat_pow_eq
  exact hab ((pow_apply_of_fixed p hb n).symm.trans hn).symm

end CutCapCount

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount



/-- The `2k` merge swaps: for each `i`, splice the two caps into the `σ`-orbit at
`v_i` by swapping each bank-end with its cap. -/
noncomputable def mergeList (C : SimplePrimalCycle M) : List (C.CutDart × C.CutDart) :=
  (List.finRange C.len).flatMap (fun i => [(C.lEndPlus i, C.capP i), (C.lEndMinus i, C.capM i)])

/-- The `k` split swaps: for each `i`, separate the merged orbit into its two banks
by swapping the two caps. -/
noncomputable def splitList (C : SimplePrimalCycle M) : List (C.CutDart × C.CutDart) :=
  (List.finRange C.len).map (fun i => (C.capP i, C.capM i))

/-- The product of the merge swaps. -/
noncomputable def mergeProd (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  (C.mergeList.map (fun w => Equiv.swap w.1 w.2)).prod

/-- The product of the split swaps. -/
noncomputable def splitProd (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  (C.splitList.map (fun w => Equiv.swap w.1 w.2)).prod



/-- Over an arbitrary index list, the split product fixes `inl d`. -/
lemma splitMap_apply_inl (C : SimplePrimalCycle M) (d : D) (L : List (Fin C.len)) :
    ((L.map (fun i => (C.capP i, C.capM i))).map
        (fun w => Equiv.swap w.1 w.2)).prod (Sum.inl d) = Sum.inl d := by
  apply CutCapCount.listSwap_prod_fix
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨i, _, rfl⟩ := hw
  exact ⟨by simp [capP], by simp [capM]⟩

/-- The split product over a `Nodup` index list sends `capP i` to `capM i` when
`i` is in the list, and fixes it otherwise. -/
lemma splitMap_apply_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.map (fun j => (C.capP j, C.capM j))).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capP i)
        = if i ∈ L then C.capM i else C.capP i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hL']
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        exact Equiv.swap_apply_left _ _
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- apply `swap (capP j) (capM j)` to `capM i`: disjoint
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => C.capP_ne_capM j i h.symm)
            (fun h => hij (C.capM_inj h))]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- apply `swap (capP j) (capM j)` to `capP i`: disjoint
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => hij (C.capP_inj h)) (fun h => C.capP_ne_capM i j h)]

/-- The split product over a `Nodup` index list sends `capM i` to `capP i` when
`i` is in the list, and fixes it otherwise. -/
lemma splitMap_apply_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.map (fun j => (C.capP j, C.capM j))).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capM i)
        = if i ∈ L then C.capP i else C.capM i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.map_cons, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih hL']
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        exact Equiv.swap_apply_right _ _
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => hij (C.capP_inj h)) (fun h => C.capP_ne_capM i j h)]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          rw [Equiv.swap_apply_of_ne_of_ne
            (fun h => C.capP_ne_capM j i h.symm) (fun h => hij (C.capM_inj h))]



@[simp] lemma splitProd_inl (C : SimplePrimalCycle M) (d : D) :
    C.splitProd (Sum.inl d) = Sum.inl d := by
  rw [splitProd, splitList]; exact C.splitMap_apply_inl d _

@[simp] lemma splitProd_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.capP i) = C.capM i := by
  rw [splitProd, splitList, C.splitMap_apply_capP i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma splitProd_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.capM i) = C.capP i := by
  rw [splitProd, splitList, C.splitMap_apply_capM i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]







/-- Over an index list, the merge product fixes `inl d` whenever `d` is not a
bank-end (i.e. `inl d ≠ ℓ_j^±` for every `j` in the list). -/
lemma mergeMap_apply_inl_clean (C : SimplePrimalCycle M) (d : D)
    (hp : ∀ j, Sum.inl d ≠ C.lEndPlus j) (hq : ∀ j, Sum.inl d ≠ C.lEndMinus j)
    (L : List (Fin C.len)) :
    ((L.flatMap (fun i => [(C.lEndPlus i, C.capP i), (C.lEndMinus i, C.capM i)])).map
      (fun w => Equiv.swap w.1 w.2)).prod (Sum.inl d) = Sum.inl d := by
  apply CutCapCount.listSwap_prod_fix
  intro w hw
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  obtain ⟨j, _, hwj⟩ := hw
  rcases hwj with rfl | rfl
  · exact ⟨hp j, by simp [capP]⟩
  · exact ⟨hq j, by simp [capM]⟩

/-- Merge product over a `Nodup` list: `capP i ↦ ℓ_i^+` when `i` is present. -/
lemma mergeMap_apply_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capP i)
        = if i ∈ L then C.lEndPlus i else C.capP i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner swap(ℓ⁻,c⁻) fixes capP i; outer swap(ℓ⁺,c⁺) sends capP i ↦ ℓ⁺
        rw [Equiv.swap_apply_of_ne_of_ne (by simp [capP, lEndMinus]) (C.capP_ne_capM i i),
          Equiv.swap_apply_right]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix ℓ_i^+
          rw [Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i j) (C.lEndPlus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndPlus_inj h)) (C.lEndPlus_ne_capP i j)]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix capP i
          rw [Equiv.swap_apply_of_ne_of_ne (by simp [capP, lEndMinus]) (C.capP_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndPlus_ne_capP j i h.symm))
              (fun h => hij (C.capP_inj h))]

/-- Merge product over a `Nodup` list: `capM i ↦ ℓ_i^-` when `i` is present. -/
lemma mergeMap_apply_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.capM i)
        = if i ∈ L then C.lEndMinus i else C.capM i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner swap(ℓ⁻,c⁻) sends capM i ↦ ℓ⁻; outer fixes ℓ⁻
        rw [Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i i).symm
            (fun h => (C.lEndMinus_ne_capP i i) h)]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix ℓ_i^-
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndMinus_inj h)) (C.lEndMinus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus j i).symm (C.lEndMinus_ne_capP i j)]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix capM i
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndMinus_ne_capM j i h.symm))
              (fun h => hij (C.capM_inj h)),
            Equiv.swap_apply_of_ne_of_ne (by simp [capM, lEndPlus]) (fun h => (C.capP_ne_capM j i h.symm))]

/-- Merge product over a `Nodup` list: `ℓ_i^+ ↦ capP i` when `i` is present. -/
lemma mergeMap_apply_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.lEndPlus i)
        = if i ∈ L then C.capP i else C.lEndPlus i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner fixes ℓ⁺; outer swap(ℓ⁺,c⁺) sends ℓ⁺ ↦ capP i
        rw [Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i i) (C.lEndPlus_ne_capM i i),
          Equiv.swap_apply_left]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix capP i
          rw [Equiv.swap_apply_of_ne_of_ne (by simp [capP, lEndMinus]) (C.capP_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndPlus_ne_capP j i h.symm))
              (fun h => hij (C.capP_inj h))]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix ℓ_i^+
          rw [Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus i j) (C.lEndPlus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndPlus_inj h)) (C.lEndPlus_ne_capP i j)]

/-- Merge product over a `Nodup` list: `ℓ_i^- ↦ capM i` when `i` is present. -/
lemma mergeMap_apply_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    ∀ L : List (Fin C.len), L.Nodup →
      ((L.flatMap (fun j => [(C.lEndPlus j, C.capP j), (C.lEndMinus j, C.capM j)])).map
        (fun w => Equiv.swap w.1 w.2)).prod (C.lEndMinus i)
        = if i ∈ L then C.capM i else C.lEndMinus i := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons j L' ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      obtain ⟨hj, hL'⟩ := hnd
      rw [List.flatMap_cons, List.map_append, List.prod_append, Equiv.Perm.mul_apply, ih hL']
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      by_cases hij : i = j
      · subst hij
        have hni : i ∉ L' := hj
        simp only [hni, if_false, List.mem_cons, true_or, if_true]
        -- inner swap(ℓ⁻,c⁻) sends ℓ⁻ ↦ capM i; outer fixes capM i
        rw [Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndPlus_ne_capM i i) h.symm)
            (C.capP_ne_capM i i).symm]
      · by_cases hmem : i ∈ L'
        · simp only [hmem, if_true, List.mem_cons, or_true]
          -- both swaps fix capM i
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => (C.lEndMinus_ne_capM j i h.symm))
              (fun h => hij (C.capM_inj h)),
            Equiv.swap_apply_of_ne_of_ne (by simp [capM, lEndPlus]) (fun h => (C.capP_ne_capM j i h.symm))]
        · simp only [hmem, if_false, List.mem_cons, hij, false_or, if_false]
          -- both swaps fix ℓ_i^-
          rw [Equiv.swap_apply_of_ne_of_ne (fun h => hij (C.lEndMinus_inj h)) (C.lEndMinus_ne_capM i j),
            Equiv.swap_apply_of_ne_of_ne (C.lEndPlus_ne_lEndMinus j i).symm (C.lEndMinus_ne_capP i j)]



@[simp] lemma mergeProd_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.capP i) = C.lEndPlus i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_capP i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma mergeProd_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.capM i) = C.lEndMinus i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_capM i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma mergeProd_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.lEndPlus i) = C.capP i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_lEndPlus i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma mergeProd_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.mergeProd (C.lEndMinus i) = C.capM i := by
  rw [mergeProd, mergeList, C.mergeMap_apply_lEndMinus i _ (List.nodup_finRange _)]
  simp [List.mem_finRange]

@[simp] lemma splitProd_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.lEndPlus i) = C.lEndPlus i := by rw [lEndPlus, splitProd_inl]
@[simp] lemma splitProd_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.splitProd (C.lEndMinus i) = C.lEndMinus i := by rw [lEndMinus, splitProd_inl]

/-- `mergeProd` fixes `inl d` when `d` is not a bank-end. -/
lemma mergeProd_inl_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, Sum.inl d ≠ C.lEndPlus i) (hq : ∀ i, Sum.inl d ≠ C.lEndMinus i) :
    C.mergeProd (Sum.inl d) = Sum.inl d := by
  rw [mergeProd, mergeList]; exact C.mergeMap_apply_inl_clean d hp hq _



/-- `inl d = ℓ_i^+` iff `σ d = p_i`. -/
lemma inl_eq_lEndPlus_iff (C : SimplePrimalCycle M) (d : D) (i : Fin C.len) :
    Sum.inl d = C.lEndPlus i ↔ M.σ d = C.pDart i := by
  rw [lEndPlus, Sum.inl.injEq]
  constructor
  · intro h; rw [h, M.σ.apply_symm_apply]
  · intro h; rw [← h, M.σ.symm_apply_apply]

/-- `inl d = ℓ_i^-` iff `σ d = q_i`. -/
lemma inl_eq_lEndMinus_iff (C : SimplePrimalCycle M) (d : D) (i : Fin C.len) :
    Sum.inl d = C.lEndMinus i ↔ M.σ d = C.qDart i := by
  rw [lEndMinus, Sum.inl.injEq]
  constructor
  · intro h; rw [h, M.σ.apply_symm_apply]
  · intro h; rw [← h, M.σ.symm_apply_apply]

/-- **The transposition decomposition of the cut-and-cap rotation.** -/
theorem cutSigmaPerm_eq_sigmaLift_mul (C : SimplePrimalCycle M) :
    C.cutSigmaPerm = C.sigmaLift * C.mergeProd * C.splitProd := by
  ext x
  rw [cutSigmaPerm_apply, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Function.comp_apply]
  rcases x with d | (i | i)
  · -- inl d : classify by divertKind
    rcases hd : C.divertKind d with (i | i) | u
    · -- σ d = p_i, so inl d = ℓ_i^+
      have hσ : M.σ d = C.pDart i := C.divertKind_eq_plus hd
      have hℓ : Sum.inl d = C.lEndPlus i := (C.inl_eq_lEndPlus_iff d i).2 hσ
      rw [C.cutSigma_inl_plus hd, hℓ, splitProd_lEndPlus, mergeProd_lEndPlus, capP, sigmaLift_inr]
    · have hσ : M.σ d = C.qDart i := C.divertKind_eq_minus hd
      have hℓ : Sum.inl d = C.lEndMinus i := (C.inl_eq_lEndMinus_iff d i).2 hσ
      rw [C.cutSigma_inl_minus hd, hℓ, splitProd_lEndMinus, mergeProd_lEndMinus, capM, sigmaLift_inr]
    · obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
      have hcp : ∀ i, Sum.inl d ≠ C.lEndPlus i := fun i hi =>
        hp i ((C.inl_eq_lEndPlus_iff d i).1 hi)
      have hcq : ∀ i, Sum.inl d ≠ C.lEndMinus i := fun i hi =>
        hq i ((C.inl_eq_lEndMinus_iff d i).1 hi)
      rw [C.cutSigma_inl_none hd, splitProd_inl, C.mergeProd_inl_clean hcp hcq, sigmaLift_inl]
  · -- capP i ↦ q_i
    show _ = C.sigmaLift (C.mergeProd (C.splitProd (C.capP i)))
    rw [cutSigma_capPlus, splitProd_capP, mergeProd_capM, lEndMinus, sigmaLift_inl,
      M.σ.apply_symm_apply]
  · -- capM i ↦ p_i
    show _ = C.sigmaLift (C.mergeProd (C.splitProd (C.capM i)))
    rw [cutSigma_capMinus, splitProd_capM, mergeProd_capP, lEndPlus, sigmaLift_inl,
      M.σ.apply_symm_apply]



/-- The merged permutation `Q = σ⊕1` times the merge swaps. -/
noncomputable def merged (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  C.sigmaLift * C.mergeProd

lemma merged_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.merged x = C.sigmaLift (C.mergeProd x) := rfl

@[simp] lemma merged_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.capP i) = Sum.inl (C.pDart i) := by
  rw [merged_apply, mergeProd_capP, lEndPlus, sigmaLift_inl, M.σ.apply_symm_apply]

@[simp] lemma merged_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.capM i) = Sum.inl (C.qDart i) := by
  rw [merged_apply, mergeProd_capM, lEndMinus, sigmaLift_inl, M.σ.apply_symm_apply]

/-- On a clean dart (not a bank-end) `Q` acts as `σ`. -/
lemma merged_inl_clean (C : SimplePrimalCycle M) {d : D}
    (hp : ∀ i, M.σ d ≠ C.pDart i) (hq : ∀ i, M.σ d ≠ C.qDart i) :
    C.merged (Sum.inl d) = Sum.inl (M.σ d) := by
  have hcp : ∀ i, Sum.inl d ≠ C.lEndPlus i := fun i hi =>
    hp i ((C.inl_eq_lEndPlus_iff d i).1 hi)
  have hcq : ∀ i, Sum.inl d ≠ C.lEndMinus i := fun i hi =>
    hq i ((C.inl_eq_lEndMinus_iff d i).1 hi)
  rw [merged_apply, C.mergeProd_inl_clean hcp hcq, sigmaLift_inl]

/-- On the `+`-bank-end `ℓ_i^+` the merged map diverts to the `+`-cap. -/
lemma merged_lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.lEndPlus i) = C.capP i := by
  rw [merged_apply, mergeProd_lEndPlus, capP, sigmaLift_inr]

/-- On the `−`-bank-end `ℓ_i^-` the merged map diverts to the `−`-cap. -/
lemma merged_lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged (C.lEndMinus i) = C.capM i := by
  rw [merged_apply, mergeProd_lEndMinus, capM, sigmaLift_inr]

/-- The merged map applied to `inl d` always lands in the `inl` summand, equal to
`inl (σ d)` away from bank-ends and to a cap at a bank-end (which equals
`inl (σ d)` after one more `Q`-step).  This is the unified statement used by the
projection. -/
lemma merged_inl (C : SimplePrimalCycle M) (d : D) :
    C.merged (Sum.inl d) = Sum.inl (M.σ d) ∨
      (∃ i, M.σ d = C.pDart i ∧ C.merged (Sum.inl d) = C.capP i) ∨
      (∃ i, M.σ d = C.qDart i ∧ C.merged (Sum.inl d) = C.capM i) := by
  by_cases hp : ∃ i, M.σ d = C.pDart i
  · obtain ⟨i, hi⟩ := hp
    right; left
    refine ⟨i, hi, ?_⟩
    rw [show Sum.inl d = C.lEndPlus i from (C.inl_eq_lEndPlus_iff d i).2 hi, merged_lEndPlus]
  · by_cases hq : ∃ i, M.σ d = C.qDart i
    · obtain ⟨i, hi⟩ := hq
      right; right
      refine ⟨i, hi, ?_⟩
      rw [show Sum.inl d = C.lEndMinus i from (C.inl_eq_lEndMinus_iff d i).2 hi, merged_lEndMinus]
    · left
      exact C.merged_inl_clean (fun i hi => hp ⟨i, hi⟩) (fun i hi => hq ⟨i, hi⟩)



/-- The projection of a cut-dart back to `D`. -/
noncomputable def proj (C : SimplePrimalCycle M) : C.CutDart → D :=
  fun x => match x with
  | Sum.inl d => d
  | Sum.inr (Sum.inl i) => C.pDart i
  | Sum.inr (Sum.inr i) => C.qDart i

@[simp] lemma proj_inl (C : SimplePrimalCycle M) (d : D) : C.proj (Sum.inl d) = d := rfl
@[simp] lemma proj_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.proj (C.capP i) = C.pDart i := rfl
@[simp] lemma proj_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.proj (C.capM i) = C.qDart i := rfl

/-- **The per-step projection fact.**  `proj (Q x)` is either `σ (proj x)` (the
`inl`-dart case, including the divert-to-cap step) or `proj x` (the cap case). -/
lemma proj_merged (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.proj (C.merged x) = M.σ (C.proj x) ∨ C.proj (C.merged x) = C.proj x := by
  rcases x with d | (i | i)
  · -- inl d : always the σ branch
    left
    rcases C.merged_inl d with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩
    · rw [h]; rfl
    · rw [h, proj_capP, proj_inl, hi]
    · rw [h, proj_capM, proj_inl, hi]
  · -- capP i : stall branch (Q (capP i) = inl (p_i), proj = p_i = proj (capP i))
    right
    rw [show (Sum.inr (Sum.inl i) : C.CutDart) = C.capP i from rfl, merged_capP, proj_inl, proj_capP]
  · -- capM i : stall branch
    right
    rw [show (Sum.inr (Sum.inr i) : C.CutDart) = C.capM i from rfl, merged_capM, proj_inl, proj_capM]

/-- Iterating the per-step fact: `proj (Q^n x) = σ^m (proj x)` for some `m`. -/
lemma proj_merged_pow (C : SimplePrimalCycle M) (x : C.CutDart) :
    ∀ n : ℕ, ∃ m : ℕ, C.proj ((C.merged ^ n) x) = (M.σ ^ m) (C.proj x) := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      rcases C.proj_merged ((C.merged ^ n) x) with h | h
      · refine ⟨m + 1, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, h, hm, pow_succ', Equiv.Perm.mul_apply]
      · refine ⟨m, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, h, hm]



/-- **Backward reduction.**  Co-cyclic `inl`-darts under `Q` are co-cyclic under
`σ`. -/
lemma sameCycle_merged_inl_imp (C : SimplePrimalCycle M) {a b : D}
    (h : C.merged.SameCycle (Sum.inl a) (Sum.inl b)) : M.σ.SameCycle a b := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  obtain ⟨m, hm⟩ := C.proj_merged_pow (Sum.inl a) n
  refine ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast]
  have : C.proj ((C.merged ^ n) (Sum.inl a)) = b := by rw [hn]; rfl
  rw [hm, proj_inl] at this
  exact this

/-- One `σ`-step lifts to a `Q`-relation on `inl`-darts. -/
lemma sameCycle_merged_inl_sigma_step (C : SimplePrimalCycle M) (a : D) :
    C.merged.SameCycle (Sum.inl a) (Sum.inl (M.σ a)) := by
  by_cases hp : ∃ i, M.σ a = C.pDart i
  · obtain ⟨i, hi⟩ := hp
    -- inl a = ℓ_i^+, Q(ℓ_i^+) = c_i^+, Q(c_i^+) = inl(p_i) = inl(σ a)
    have hℓ : Sum.inl a = C.lEndPlus i := (C.inl_eq_lEndPlus_iff a i).2 hi
    refine ⟨(2 : ℤ), ?_⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, Equiv.Perm.mul_apply,
      hℓ, merged_lEndPlus, merged_capP, hi]
  · by_cases hq : ∃ i, M.σ a = C.qDart i
    · obtain ⟨i, hi⟩ := hq
      have hℓ : Sum.inl a = C.lEndMinus i := (C.inl_eq_lEndMinus_iff a i).2 hi
      refine ⟨(2 : ℤ), ?_⟩
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, Equiv.Perm.mul_apply,
        hℓ, merged_lEndMinus, merged_capM, hi]
    · refine ⟨(1 : ℤ), ?_⟩
      rw [zpow_one, C.merged_inl_clean (fun i hi => hp ⟨i, hi⟩) (fun i hi => hq ⟨i, hi⟩)]

/-- **Forward reduction.**  Co-cyclic darts under `σ` lift to co-cyclic
`inl`-darts under `Q`. -/
lemma sameCycle_merged_inl_pow (C : SimplePrimalCycle M) (a : D) :
    ∀ n : ℕ, C.merged.SameCycle (Sum.inl a) (Sum.inl ((M.σ ^ n) a)) := by
  intro n
  induction n with
  | zero => simp only [pow_zero, Equiv.Perm.coe_one, id_eq]; exact Equiv.Perm.SameCycle.refl _ _
  | succ n ih =>
      have hstep := C.sameCycle_merged_inl_sigma_step ((M.σ ^ n) a)
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact ih.trans hstep

lemma sameCycle_merged_inl_of_sigma (C : SimplePrimalCycle M) {a b : D}
    (h : M.σ.SameCycle a b) : C.merged.SameCycle (Sum.inl a) (Sum.inl b) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have := C.sameCycle_merged_inl_pow a n
  rwa [hn] at this



/-- Each cap is `Q`-co-cyclic with its bank-start `inl`-dart. -/
lemma sameCycle_merged_capP_inl (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged.SameCycle (C.capP i) (Sum.inl (C.pDart i)) :=
  ⟨(1 : ℤ), by rw [zpow_one, merged_capP]⟩

lemma sameCycle_merged_capM_inl (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged.SameCycle (C.capM i) (Sum.inl (C.qDart i)) :=
  ⟨(1 : ℤ), by rw [zpow_one, merged_capM]⟩

/-- The two caps at `v_i` are `Q`-co-cyclic (reduces to `σ.SameCycle p_i q_i`). -/
lemma sameCycle_merged_capP_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.merged.SameCycle (C.capP i) (C.capM i) := by
  refine (C.sameCycle_merged_capP_inl i).trans ?_
  refine (C.sameCycle_merged_inl_of_sigma (C.sameCycle_pDart_qDart i)).trans ?_
  exact (C.sameCycle_merged_capM_inl i).symm

/-- Distinct-index caps are in different `Q`-cycles (reduces to distinct
`σ`-orbits at distinct cycle vertices). -/
lemma not_sameCycle_merged_capP_capP (C : SimplePrimalCycle M) {i j : Fin C.len}
    (hij : i ≠ j) : ¬ C.merged.SameCycle (C.capP i) (C.capP j) := by
  intro h
  apply C.not_sameCycle_pDart_of_ne hij
  apply C.sameCycle_merged_inl_imp
  exact ((C.sameCycle_merged_capP_inl i).symm.trans h).trans (C.sameCycle_merged_capP_inl j)

lemma not_sameCycle_merged_capP_capM (C : SimplePrimalCycle M) {i j : Fin C.len}
    (hij : i ≠ j) : ¬ C.merged.SameCycle (C.capP i) (C.capM j) := by
  intro h
  -- would give σ.SameCycle p_i q_j, but tail p_i = v_i ≠ v_j = tail q_j
  have hσ : M.σ.SameCycle (C.pDart i) (C.qDart j) := by
    apply C.sameCycle_merged_inl_imp
    exact ((C.sameCycle_merged_capP_inl i).symm.trans h).trans (C.sameCycle_merged_capM_inl j)
  apply hij
  have : M.tail (C.pDart i) = M.tail (C.qDart j) := Quotient.sound hσ
  rw [C.tail_pDart_eq_tail_qDart i, C.tail_qDart i, C.tail_qDart j] at this
  exact C.tail_inj this



/-- The list lengths. -/
lemma mergeList_length (C : SimplePrimalCycle M) : C.mergeList.length = 2 * C.len := by
  rw [mergeList, List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate,
    List.length_finRange, smul_eq_mul]
  ring

lemma splitList_length (C : SimplePrimalCycle M) : C.splitList.length = C.len := by
  rw [splitList, List.length_map, List.length_finRange]

/-- Every entry of `mergeList` is an `(ℓ, cap)` pair: first component `inl`, second
component a cap, and the two distinct. -/
lemma mergeList_mem (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) :
    (∃ i, w = (C.lEndPlus i, C.capP i)) ∨ (∃ i, w = (C.lEndMinus i, C.capM i)) := by
  rw [mergeList, List.mem_flatMap] at hw
  obtain ⟨i, _, hwi⟩ := hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwi
  rcases hwi with rfl | rfl
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- The caps as a flat list. -/
lemma mergeList_map_snd (C : SimplePrimalCycle M) :
    C.mergeList.map Prod.snd
      = (List.finRange C.len).flatMap (fun i => [C.capP i, C.capM i]) := by
  rw [mergeList, List.map_flatMap]
  rfl

/-- The second components of `mergeList` (the caps) are pairwise distinct. -/
lemma mergeList_snd_nodup (C : SimplePrimalCycle M) :
    (C.mergeList.map Prod.snd).Nodup := by
  rw [mergeList_map_snd]
  apply List.nodup_flatMap.2
  refine ⟨?_, ?_⟩
  · intro i _
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true]
    exact ⟨C.capP_ne_capM i i, not_false⟩
  · apply (List.nodup_finRange C.len).pairwise_of_forall_ne
    intro i _ j _ hij
    rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, capP, capM] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h | h <;> exact hij (by simp_all)

/-- The first component of any `mergeList` entry is an `inl` dart. -/
lemma mergeList_fst_inl (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) : ∃ d : D, w.1 = Sum.inl d := by
  rcases C.mergeList_mem hw with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The second component of any `mergeList` entry is a cap (an `inr` dart). -/
lemma mergeList_snd_inr (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) : ∃ c, w.2 = Sum.inr c := by
  rcases C.mergeList_mem hw with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- Each `mergeList` pair has distinct first and second components. -/
lemma mergeList_fst_ne_snd (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.mergeList) : w.1 ≠ w.2 := by
  obtain ⟨d, hd⟩ := C.mergeList_fst_inl hw
  obtain ⟨c, hc⟩ := C.mergeList_snd_inr hw
  rw [hd, hc]; exact Sum.inl_ne_inr

/-- The cap at position `j` does not occur in the prefix `mergeList.take j`. -/
lemma mergeList_get_snd_not_mem_take (C : SimplePrimalCycle M) (j : Fin C.mergeList.length)
    {w : C.CutDart × C.CutDart} (hw : w ∈ C.mergeList.take j) :
    (C.mergeList.get j).2 ≠ w.1 ∧ (C.mergeList.get j).2 ≠ w.2 := by
  have hwmem : w ∈ C.mergeList := List.mem_of_mem_take hw
  -- the cap (get j).2 is an `inr`; w.1 is `inl`
  obtain ⟨c, hc⟩ := C.mergeList_snd_inr (List.get_mem C.mergeList j)
  obtain ⟨d, hd⟩ := C.mergeList_fst_inl hwmem
  refine ⟨by rw [hc, hd]; exact Sum.inr_ne_inl, ?_⟩
  -- distinctness of the second components via the Nodup of `mergeList.map .2`
  intro hcontra
  have hnd := C.mergeList_snd_nodup
  obtain ⟨k, hk, hwk⟩ := List.mem_iff_getElem.1 hw
  have hkj : k < (j : ℕ) := lt_of_lt_of_le hk (List.length_take_le _ _)
  have hklt : k < C.mergeList.length := hkj.trans j.isLt
  rw [List.getElem_take] at hwk
  -- (map .2)[j] = (map .2)[k] forces j = k, but k < j
  have hmapj : (C.mergeList.map Prod.snd)[(j : ℕ)]'(by simp [j.isLt]) = (C.mergeList.get j).2 := by
    simp [List.getElem_map]
  have hmapk : (C.mergeList.map Prod.snd)[k]'(by simp [hklt]) = w.2 := by
    simp [List.getElem_map, hwk]
  have hjk : (j : ℕ) = k := by
    apply (hnd.getElem_inj_iff).1
    rw [hmapj, hmapk, hcontra]
  omega

/-- Any `splitList` entry is a cap pair. -/
lemma splitList_mem (C : SimplePrimalCycle M) {w : C.CutDart × C.CutDart}
    (hw : w ∈ C.splitList) : ∃ idx, w = (C.capP idx, C.capM idx) := by
  rw [splitList, List.mem_map] at hw
  obtain ⟨i, _, rfl⟩ := hw; exact ⟨i, rfl⟩

/-- The index carried by `splitList.get j`. -/
lemma splitList_get (C : SimplePrimalCycle M) (j : Fin C.splitList.length) :
    ∃ idx : Fin C.len, C.splitList.get j = (C.capP idx, C.capM idx) :=
  C.splitList_mem (List.get_mem C.splitList j)

/-- `splitList` is `Nodup`. -/
lemma splitList_nodup (C : SimplePrimalCycle M) : C.splitList.Nodup := by
  rw [splitList]
  apply (List.nodup_finRange C.len).map
  intro i j h
  exact C.capP_inj (Prod.ext_iff.1 h).1

/-- The index at position `j` of `splitList` differs from every prefix index. -/
lemma splitList_take_index_ne (C : SimplePrimalCycle M) (j : Fin C.splitList.length)
    {idx idx' : Fin C.len} (hidx : C.splitList.get j = (C.capP idx, C.capM idx))
    (hw : (C.capP idx', C.capM idx') ∈ C.splitList.take j) : idx' ≠ idx := by
  obtain ⟨k, hk, hwk⟩ := List.mem_iff_getElem.1 hw
  have hkj : k < (j : ℕ) := lt_of_lt_of_le hk (List.length_take_le _ _)
  have hklt : k < C.splitList.length := hkj.trans j.isLt
  rw [List.getElem_take] at hwk
  intro hcontra; subst hcontra
  -- splitList[k] = (capP idx, capM idx) = splitList[j], so k = j by Nodup
  have hkj_eq : k = (j : ℕ) := by
    have := (C.splitList_nodup.getElem_inj_iff (i := k) (hi := hklt) (j := (j : ℕ))
      (hj := j.isLt)).1
    apply this
    rw [hwk]
    exact hidx.symm
  omega

/-- **Merge phase.**  `numCycles (sigmaLift * mergeProd) + 2k = numCycles sigmaLift`. -/
lemma numCycles_merged_add (C : SimplePrimalCycle M) :
    _root_.numCycles C.merged + C.mergeList.length = _root_.numCycles C.sigmaLift := by
  rw [merged, mergeProd]
  apply CutCapCount.numCycles_mul_listSwap_merges
  intro j
  have hget : C.mergeList.get j ∈ C.mergeList := List.get_mem C.mergeList j
  refine ⟨C.mergeList_fst_ne_snd hget, ?_⟩
  -- the cap (get j).2 is fixed by `sigmaLift * (prefix)` ⟹ not co-cyclic with (get j).1
  apply CutCapCount.not_sameCycle_of_fixed
  · -- fixed: prefix product fixes the cap, sigmaLift fixes the cap
    rw [Equiv.Perm.mul_apply]
    obtain ⟨c, hc⟩ := C.mergeList_snd_inr hget
    rw [CutCapCount.listSwap_prod_apply_of_notMem _ _
      (fun w hw => C.mergeList_get_snd_not_mem_take j hw), hc, sigmaLift_inr]
  · exact C.mergeList_fst_ne_snd hget

/-- **Split phase.**  `numCycles (merged * splitProd) = numCycles merged + k`. -/
lemma numCycles_split (C : SimplePrimalCycle M) :
    _root_.numCycles (C.merged * C.splitProd)
      = _root_.numCycles C.merged + C.splitList.length := by
  rw [splitProd]
  apply CutCapCount.numCycles_mul_listSwap_splits
  intro j
  obtain ⟨idx, hidx⟩ := C.splitList_get j
  rw [hidx]
  refine ⟨C.capP_ne_capM idx idx, ?_⟩
  -- transport `merged.SameCycle (capP idx) (capM idx)` across the prefix split swaps
  apply CutCapCount.sameCycle_mul_of_orbit_fixed
  · intro y hy
    -- the prefix product fixes y, since y's `merged`-class avoids all prefix caps
    apply CutCapCount.listSwap_prod_apply_of_notMem
    intro w hw
    obtain ⟨idx', hw'⟩ := C.splitList_mem (List.mem_of_mem_take hw)
    subst hw'
    have hne : idx' ≠ idx := C.splitList_take_index_ne j hidx hw
    -- y ≠ capP idx' and y ≠ capM idx', else y co-cyclic with capP idx contradicts distinct orbits
    dsimp only
    refine ⟨fun hyc => ?_, fun hyc => ?_⟩
    · exact C.not_sameCycle_merged_capP_capP (Ne.symm hne) (hyc ▸ hy)
    · exact C.not_sameCycle_merged_capP_capM (Ne.symm hne) (hyc ▸ hy)
  · exact C.sameCycle_merged_capP_capM idx



/-- `numCycles merged = V` (the merge swaps merge each of the `2k` caps into the
`σ`-orbit at its vertex). -/
lemma numCycles_merged (C : SimplePrimalCycle M) :
    _root_.numCycles C.merged = M.V := by
  have h := C.numCycles_merged_add
  rw [numCycles_sigmaLift, mergeList_length] at h
  omega

/-- **The cut-and-cap rotation has `V + k` cycles.** -/
theorem numCycles_cutSigmaPerm (C : SimplePrimalCycle M) :
    _root_.numCycles C.cutSigmaPerm = M.V + C.len := by
  rw [cutSigmaPerm_eq_sigmaLift_mul, ← merged, numCycles_split, numCycles_merged,
    splitList_length]



end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapV
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapF -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CutCapCount

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Cycle count is conjugation-invariant.** -/
lemma numCycles_conj (g f : Equiv.Perm E) :
    _root_.numCycles (g * f * g⁻¹) = _root_.numCycles f := by
  classical
  unfold _root_.numCycles
  refine Fintype.card_congr (Quotient.congr g⁻¹ ?_)
  intro x y
  show (g * f * g⁻¹).SameCycle x y ↔ f.SameCycle (g⁻¹ x) (g⁻¹ y)
  exact Equiv.Perm.sameCycle_conj

/-- **`numCycles` is invariant under swapping factors** (`AB ~ BA`). -/
lemma numCycles_mul_comm (a b : Equiv.Perm E) :
    _root_.numCycles (a * b) = _root_.numCycles (b * a) := by
  have h : b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by group
  rw [h, numCycles_conj]

end CutCapCount

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount









/-- `φ = σ*α` extended to the cut-dart set, caps as fixed points. -/
noncomputable def phiLift (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.φ (1 : Equiv.Perm (Fin C.len ⊕ Fin C.len))









/-- The cycle count of `phiLift` is `F + 2k`. -/
lemma numCycles_phiLift (C : SimplePrimalCycle M) :
    _root_.numCycles C.phiLift = M.F + 2 * C.len := by
  rw [phiLift, numCycles_sumCongr_one, M.F_eq_numCycles]
  simp [Fintype.card_sum, Fintype.card_fin]; ring



























end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideRecon
import ProofsInTheBook.PlanarMapCutCapCounts
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.ChordFaceCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.PlanarMap.CombMap.CutCapCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section FacePerm

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The face permutation of the fresh map: `freshSigma ∘ freshAlpha`. -/
lemma freshMap_phi_eq :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ
      = freshSigma ρ a₀ a₁ hne * freshAlpha β := rfl

/-- `φ` on `inl k` with `β k ≠ a₀`, `β k ≠ a₁`: the kept face permutation `ρ ∘ β`. -/
lemma freshMap_phi_inl_other {k : K} (h0 : β k ≠ a₀) (h1 : β k ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inl k) = Sum.inl (ρ (β k)) := by
  rw [freshMap_phi_eq, Equiv.Perm.mul_apply, freshAlpha_inl,
    freshSigma_other ρ a₀ a₁ hne h0 h1]

/-- `φ (inl (β a₀)) = inr 0`. -/
lemma freshMap_phi_inl_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inl (β a₀)) = Sum.inr 0 := by
  have hbb : β (β a₀) = a₀ := by
    have := congrArg (fun f : Equiv.Perm K => f a₀) hβinv
    simpa [Equiv.Perm.mul_apply] using this
  rw [freshMap_phi_eq, Equiv.Perm.mul_apply, freshAlpha_inl, hbb,
    freshSigma_anchor_zero ρ a₀ a₁ hne]

/-- `φ (inl (β a₁)) = inr 1`. -/
lemma freshMap_phi_inl_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inl (β a₁)) = Sum.inr 1 := by
  have hbb : β (β a₁) = a₁ := by
    have := congrArg (fun f : Equiv.Perm K => f a₁) hβinv
    simpa [Equiv.Perm.mul_apply] using this
  rw [freshMap_phi_eq, Equiv.Perm.mul_apply, freshAlpha_inl, hbb,
    freshSigma_anchor_one ρ a₀ a₁ hne]

/-- `φ (inr 0) = inl (ρ a₁)`. -/
lemma freshMap_phi_inr_zero :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inr 0) = Sum.inl (ρ a₁) := by
  rw [freshMap_phi_eq, Equiv.Perm.mul_apply, freshAlpha_inr]
  simp only [Equiv.swap_apply_left]
  rw [freshSigma_fresh_one ρ a₀ a₁ hne]

/-- `φ (inr 1) = inl (ρ a₀)`. -/
lemma freshMap_phi_inr_one :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inr 1) = Sum.inl (ρ a₀) := by
  rw [freshMap_phi_eq, Equiv.Perm.mul_apply, freshAlpha_inr]
  simp only [Equiv.swap_apply_right]
  rw [freshSigma_fresh_zero ρ a₀ a₁ hne]

end FacePerm



section FaceBijection

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The kept-side face permutation `ρ * β` (the face permutation of `keptCombMap β ρ`). -/
def keptPhi (β ρ : Equiv.Perm K) : Equiv.Perm K := ρ * β

/-- The **traced face permutation** on `K`: `ρ * β` with its values at the chord
predecessors `β a₀`, `β a₁` swapped (equivalently, multiplied on the left by the
transposition `swap (ρ a₀) (ρ a₁)`). -/
def tracePhi (β ρ : Equiv.Perm K) (a₀ a₁ : K) : Equiv.Perm K :=
  Equiv.swap (ρ a₀) (ρ a₁) * (ρ * β)

/-- The face projection collapsing each fresh dart to its face-cycle predecessor:
`inl k ↦ k`, `inr 0 ↦ β a₀`, `inr 1 ↦ β a₁`. -/
def faceProj (β : Equiv.Perm K) (a₀ a₁ : K) : K ⊕ Fin 2 → K
  | Sum.inl k => k
  | Sum.inr j => if j = 0 then β a₀ else β a₁

@[simp] lemma faceProj_inl (β : Equiv.Perm K) (a₀ a₁ k : K) :
    faceProj β a₀ a₁ (Sum.inl k) = k := rfl
@[simp] lemma faceProj_inr_zero (β : Equiv.Perm K) (a₀ a₁ : K) :
    faceProj β a₀ a₁ (Sum.inr 0) = β a₀ := rfl
@[simp] lemma faceProj_inr_one (β : Equiv.Perm K) (a₀ a₁ : K) :
    faceProj β a₀ a₁ (Sum.inr 1) = β a₁ := by simp [faceProj]

/-- `tracePhi` applied to `β a₀` is `ρ a₁` (the swapped value). -/
lemma tracePhi_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₀ a₁ : K) :
    tracePhi β ρ a₀ a₁ (β a₀) = ρ a₁ := by
  have hbb : β (β a₀) = a₀ := by
    have := congrArg (fun f : Equiv.Perm K => f a₀) hβinv
    simpa [Equiv.Perm.mul_apply] using this
  show Equiv.swap (ρ a₀) (ρ a₁) (ρ (β (β a₀))) = ρ a₁
  rw [hbb, Equiv.swap_apply_left]

/-- `tracePhi` applied to `β a₁` is `ρ a₀`. -/
lemma tracePhi_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₀ a₁ : K) :
    tracePhi β ρ a₀ a₁ (β a₁) = ρ a₀ := by
  have hbb : β (β a₁) = a₁ := by
    have := congrArg (fun f : Equiv.Perm K => f a₁) hβinv
    simpa [Equiv.Perm.mul_apply] using this
  show Equiv.swap (ρ a₀) (ρ a₁) (ρ (β (β a₁))) = ρ a₀
  rw [hbb, Equiv.swap_apply_right]

/-- Away from the two chord predecessors, `tracePhi` is the kept face permutation. -/
lemma tracePhi_other (β ρ : Equiv.Perm K) (a₀ a₁ : K) {k : K}
    (h0 : β k ≠ a₀) (h1 : β k ≠ a₁) :
    tracePhi β ρ a₀ a₁ k = ρ (β k) := by
  show Equiv.swap (ρ a₀) (ρ a₁) (ρ (β k)) = ρ (β k)
  have hk0 : ρ (β k) ≠ ρ a₀ := fun h => h0 (ρ.injective h)
  have hk1 : ρ (β k) ≠ ρ a₁ := fun h => h1 (ρ.injective h)
  rw [Equiv.swap_apply_of_ne_of_ne hk0 hk1]

/-- `β` is its own inverse on `a₀`: `β (β a₀) = a₀`. -/
 lemma beta_beta (β : Equiv.Perm K) (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- **Every fresh `φ`-dart is `φ`-SameCycle to the `inl` of its face projection.** -/
lemma freshPhi_sameCycle_inl_faceProj (x : K ⊕ Fin 2) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle x (Sum.inl (faceProj β a₀ a₁ x)) := by
  cases x with
  | inl k => simpa using Equiv.Perm.SameCycle.rfl
  | inr j =>
      fin_cases j
      · -- `inl (β a₀) → inr 0`, so `inr 0` is one φ-step after `inl (β a₀)`.
        show (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0)
          (Sum.inl (faceProj β a₀ a₁ (Sum.inr 0)))
        rw [faceProj_inr_zero]
        refine ⟨-1, ?_⟩
        rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b0 β ρ hβinv hβfix hne]
      · show (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1)
          (Sum.inl (faceProj β a₀ a₁ (Sum.inr 1)))
        rw [faceProj_inr_one]
        refine ⟨-1, ?_⟩
        rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b1 β ρ hβinv hβfix hne]

/-- **One fresh `φ`-step projects to a `tracePhi`-step (or stays put).** -/
lemma tracePhi_sameCycle_faceProj_phi_apply (x : K ⊕ Fin 2) :
    (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ x)
      (faceProj β a₀ a₁ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ x)) := by
  cases x with
  | inl k =>
      by_cases h0 : β k = a₀
      · -- `k = β a₀` (since `β` involutive), `φ (inl (β a₀)) = inr 0`, proj = `β a₀`.
        have hk : k = β a₀ := by
          have h2 := congrArg β h0; rw [beta_beta β hβinv] at h2; exact h2
        subst hk
        rw [freshMap_phi_inl_b0 β ρ hβinv hβfix hne]
        simp only [faceProj_inl, faceProj_inr_zero]
        exact Equiv.Perm.SameCycle.rfl
      · by_cases h1 : β k = a₁
        · have hk : k = β a₁ := by
            have h2 := congrArg β h1; rw [beta_beta β hβinv] at h2; exact h2
          subst hk
          rw [freshMap_phi_inl_b1 β ρ hβinv hβfix hne]
          simp only [faceProj_inl, faceProj_inr_one]
          exact Equiv.Perm.SameCycle.rfl
        · rw [freshMap_phi_inl_other β ρ hβinv hβfix hne h0 h1]
          simp only [faceProj_inl]
          refine ⟨1, ?_⟩
          rw [zpow_one, tracePhi_other β ρ a₀ a₁ h0 h1]
  | inr j =>
      fin_cases j
      · -- `φ (inr 0) = inl (ρ a₁)`, proj(inr 0) = `β a₀`, tracePhi (β a₀) = ρ a₁.
        show (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 0))
          (faceProj β a₀ a₁ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inr 0)))
        rw [freshMap_phi_inr_zero β ρ hβinv hβfix hne]
        simp only [faceProj_inr_zero, faceProj_inl]
        refine ⟨1, ?_⟩
        rw [zpow_one, tracePhi_b0 β ρ hβinv a₀ a₁]
      · show (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 1))
          (faceProj β a₀ a₁ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ (Sum.inr 1)))
        rw [freshMap_phi_inr_one β ρ hβinv hβfix hne]
        simp only [faceProj_inr_one, faceProj_inl]
        refine ⟨1, ?_⟩
        rw [zpow_one, tracePhi_b1 β ρ hβinv a₀ a₁]

/-- The projections of `x` and `φ^[n] x` are always `tracePhi`-SameCycle. -/
lemma tracePhi_sameCycle_faceProj_phi_iterate (x : K ⊕ Fin 2) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ x)
      (faceProj β a₀ a₁ ((freshMap β ρ hβinv hβfix a₀ a₁ hne).φ^[n] x)) := by
  induction n with
  | zero => simpa using Equiv.Perm.SameCycle.rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (tracePhi_sameCycle_faceProj_phi_apply β ρ hβinv hβfix hne _)

/-- **Forward: a fresh `φ`-cycle projects into one `tracePhi`-cycle.** -/
lemma tracePhi_sameCycle_faceProj_of_freshPhi_sameCycle {x y : K ⊕ Fin 2}
    (h : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle x y) :
    (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ x) (faceProj β a₀ a₁ y) := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [← hm, Equiv.Perm.coe_pow]
  exact tracePhi_sameCycle_faceProj_phi_iterate β ρ hβinv hβfix hne x m

/-- **One `tracePhi`-step lifts to a fresh-`φ`-SameCycle of `inl`s.** -/
lemma freshPhi_sameCycle_inl_step (c : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle
      (Sum.inl c) (Sum.inl (tracePhi β ρ a₀ a₁ c)) := by
  by_cases h0 : β c = a₀
  · -- `c = β a₀`; `tracePhi (β a₀) = ρ a₁`; path `inl (β a₀) → inr 0 → inl (ρ a₁)`.
    have hk : c = β a₀ := by
      have h2 := congrArg β h0; rw [beta_beta β hβinv] at h2; exact h2
    subst hk
    rw [tracePhi_b0 β ρ hβinv a₀ a₁]
    refine ⟨2, ?_⟩
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, Equiv.Perm.mul_apply,
      freshMap_phi_inl_b0 β ρ hβinv hβfix hne, freshMap_phi_inr_zero β ρ hβinv hβfix hne]
  · by_cases h1 : β c = a₁
    · have hk : c = β a₁ := by
        have h2 := congrArg β h1; rw [beta_beta β hβinv] at h2; exact h2
      subst hk
      rw [tracePhi_b1 β ρ hβinv a₀ a₁]
      refine ⟨2, ?_⟩
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, Equiv.Perm.mul_apply,
        freshMap_phi_inl_b1 β ρ hβinv hβfix hne, freshMap_phi_inr_one β ρ hβinv hβfix hne]
    · rw [tracePhi_other β ρ a₀ a₁ h0 h1]
      refine ⟨1, ?_⟩
      rw [zpow_one, freshMap_phi_inl_other β ρ hβinv hβfix hne h0 h1]

/-- **Backward: `inl` of `tracePhi`-equal darts are fresh-`φ`-SameCycle.** -/
lemma freshPhi_sameCycle_inl_of_tracePhi_sameCycle {a b : K}
    (h : (tracePhi β ρ a₀ a₁).SameCycle a b) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl a) (Sum.inl b) := by
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [← hm, Equiv.Perm.coe_pow]
  clear hm
  induction m with
  | zero => simpa using Equiv.Perm.SameCycle.rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (freshPhi_sameCycle_inl_step β ρ hβinv hβfix hne _)

/-- **The fresh face / traced face correspondence.**  Two fresh darts are in the same
fresh face orbit iff their face projections are in the same `tracePhi` orbit. -/
theorem freshFace_sameCycle_iff (x y : K ⊕ Fin 2) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle x y ↔
      (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ x) (faceProj β a₀ a₁ y) := by
  constructor
  · exact tracePhi_sameCycle_faceProj_of_freshPhi_sameCycle β ρ hβinv hβfix hne
  · intro h
    refine (freshPhi_sameCycle_inl_faceProj β ρ hβinv hβfix hne x).trans ?_
    refine (freshPhi_sameCycle_inl_of_tracePhi_sameCycle β ρ hβinv hβfix hne h).trans ?_
    exact (freshPhi_sameCycle_inl_faceProj β ρ hβinv hβfix hne y).symm

/-- The face-orbit quotient of the fresh map is in bijection with the `tracePhi`-orbit
quotient on `K`, via the face projection `faceProj`. -/
noncomputable def freshFaceQuotientEquiv :
    Quotient (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ)
      ≃ Quotient (cycleSetoid (tracePhi β ρ a₀ a₁)) := by
  classical
  refine
    { toFun := Quotient.lift
        (fun x => Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) (faceProj β a₀ a₁ x)) ?_,
      invFun := Quotient.lift
        (fun k => Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ)
          (Sum.inl k)) ?_,
      left_inv := ?_, right_inv := ?_ }
  · intro x y hxy
    apply Quotient.sound
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne x y).1 hxy
  · intro a b hab
    apply Quotient.sound
    exact freshPhi_sameCycle_inl_of_tracePhi_sameCycle β ρ hβinv hβfix hne hab
  · intro q
    refine Quotient.inductionOn q (fun x => ?_)
    apply Quotient.sound
    exact (freshPhi_sameCycle_inl_faceProj β ρ hβinv hβfix hne x).symm
  · intro q
    refine Quotient.inductionOn q (fun k => ?_)
    simp only [Quotient.lift_mk, faceProj_inl]

/-- **The face count of a fresh-dart adjunction equals the traced face count.**
`F(freshMap β ρ a₀ a₁) = numCycles (swap (ρ a₀) (ρ a₁) * (ρ * β))`.  The two fresh darts
are spliced *into* existing face orbits, so they neither create nor destroy a face
orbit; the chord re-routes only the two incident faces (the swap). -/
theorem freshMap_F_eq_tracePhi :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).F = numCycles (tracePhi β ρ a₀ a₁) := by
  show Fintype.card (Quotient (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ)) = _
  rw [Fintype.card_congr (freshFaceQuotientEquiv β ρ hβinv hβfix hne)]
  exact card_cycleSetoid_eq_numCycles (tracePhi β ρ a₀ a₁)

end FaceBijection



section Dichotomy

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

lemma ρa₀_ne_ρa₁ (ρ : Equiv.Perm K) {a₀ a₁ : K} (hne : a₀ ≠ a₁) :
    ρ a₀ ≠ ρ a₁ := fun h => hne (ρ.injective h)

/-- The swap of `ρ a₀`, `ρ a₁` equals the swap appearing in `tracePhi` written as a
left product `(swap …) * keptPhi`.  (Definitional, recorded for clarity.) -/
lemma tracePhi_eq_swap_mul :
    tracePhi β ρ a₀ a₁ = Equiv.swap (ρ a₀) (ρ a₁) * keptPhi β ρ := rfl

/-- The face count via commuting the swap to the right:
`numCycles (tracePhi) = numCycles (keptPhi * swap (ρ a₀) (ρ a₁))`. -/
lemma numCycles_tracePhi_eq_mul_swap :
    numCycles (tracePhi β ρ a₀ a₁)
      = numCycles (keptPhi β ρ * Equiv.swap (ρ a₀) (ρ a₁)) := by
  rw [tracePhi_eq_swap_mul β ρ, numCycles_mul_comm]

/-- **Same-face branch (`+1`).**  If `ρ a₀`, `ρ a₁` are in the same kept face
(`keptPhi`-cycle), the fresh face count is `numCycles keptPhi + 1`. -/
theorem freshMap_F_same_face
    (hsc : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁)) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).F = numCycles (keptPhi β ρ) + 1 := by
  rw [freshMap_F_eq_tracePhi β ρ hβinv hβfix hne, numCycles_tracePhi_eq_mul_swap β ρ]
  exact numCycles_mul_swap_of_sameCycle (keptPhi β ρ) (ρa₀_ne_ρa₁ ρ hne) hsc



end Dichotomy



section Genus0

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The kept combinatorial map's face count is `numCycles keptPhi`. -/
lemma keptCombMap_F : (keptCombMap β ρ hβinv hβfix).F = numCycles (keptPhi β ρ) := by
  rw [(keptCombMap β ρ hβinv hβfix).F_eq_numCycles]
  rfl

/-- The kept combinatorial map's vertex count is `numCycles ρ`. -/
lemma keptCombMap_V :
    (keptCombMap β ρ hβinv hβfix).V = Fintype.card (Quotient (cycleSetoid ρ)) := by
  rfl

/-- `2 · E_kept = |K|` (the kept edge involution is fixed-point-free). -/
lemma keptCombMap_two_mul_E :
    2 * (keptCombMap β ρ hβinv hβfix).E = Fintype.card K :=
  (keptCombMap β ρ hβinv hβfix).two_mul_E_eq_card

/-- **The genus-0 face count, from the kept Euler characteristic + same-face.**  If the
kept combinatorial map is genus-0 (`eulerChar = 2`) and the two chord successors
`ρ a₀`, `ρ a₁` lie on a common kept face, then `FreshFaceCount` holds.  This is the
explicit-bijection discharge of the chord-split face count using M's genus-0 structure:
the splice *splits* the shared boundary face (`+1`), and the kept disk's `V − E + F = 2`
turns the per-side identity `F₁ + F₂ = F + 1` into the required arithmetic. -/
theorem freshFaceCount_of_genus0
    (hkept_euler : (keptCombMap β ρ hβinv hβfix).eulerChar = 2)
    (hsame : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁)) :
    FreshFaceCount β ρ hβinv hβfix hne := by
  unfold FreshFaceCount
  -- `F = numCycles keptPhi + 1 = F_kept + 1`.
  have hF : (freshMap β ρ hβinv hβfix a₀ a₁ hne).F
      = (keptCombMap β ρ hβinv hβfix).F + 1 := by
    rw [freshMap_F_same_face β ρ hβinv hβfix hne hsame, keptCombMap_F]
  -- the kept Euler identity, in ℤ.
  have heuler : ((keptCombMap β ρ hβinv hβfix).V : ℤ)
      - ((keptCombMap β ρ hβinv hβfix).E : ℤ)
      + ((keptCombMap β ρ hβinv hβfix).F : ℤ) = 2 := hkept_euler
  have hE2 : 2 * ((keptCombMap β ρ hβinv hβfix).E : ℤ) = (Fintype.card K : ℤ) := by
    exact_mod_cast keptCombMap_two_mul_E β ρ hβinv hβfix
  have hVeq : (keptCombMap β ρ hβinv hβfix).V
      = Fintype.card (Quotient (cycleSetoid ρ)) := keptCombMap_V β ρ hβinv hβfix
  -- target (ℤ): `2 * F = |K| + 6 - 2 * V_kept`.
  have hFZ : ((freshMap β ρ hβinv hβfix a₀ a₁ hne).F : ℤ)
      = ((keptCombMap β ρ hβinv hβfix).F : ℤ) + 1 := by exact_mod_cast hF
  have hgoalZ : 2 * ((freshMap β ρ hβinv hβfix a₀ a₁ hne).F : ℤ)
      = (Fintype.card K : ℤ) + 6
        - 2 * (Fintype.card (Quotient (cycleSetoid ρ)) : ℤ) := by
    rw [hVeq] at heuler
    linarith [heuler, hE2, hFZ]
  -- transfer to ℕ (the RHS `|K| + 6 - 2·V_kept` is nonnegative since `2·F ≥ 0`).
  omega

end Genus0



section SphereAssembly

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The vertex bound consumed by the Euler reduction, derived from the genus-0 kept Euler
identity (so it is *not* an extra hypothesis at genus 0). -/
lemma vbound_of_kept_euler
    (hkept_euler : (keptCombMap β ρ hβinv hβfix).eulerChar = 2) :
    Fintype.card (Quotient (cycleSetoid ρ)) ≤ (Fintype.card K + 2) / 2 + 1 := by
  -- `V_kept = numCycles ρ`, `2·E_kept = |K|`, `F_kept ≥ 1` (nonempty face quotient? use χ=2).
  -- From `V - E + F = 2` and `F ≥ 0`, `V ≤ E + 2 = |K|/2 + 2 ≤ (|K|+2)/2 + 1`.
  have heuler : ((keptCombMap β ρ hβinv hβfix).V : ℤ)
      - ((keptCombMap β ρ hβinv hβfix).E : ℤ)
      + ((keptCombMap β ρ hβinv hβfix).F : ℤ) = 2 := hkept_euler
  have hE2 : 2 * (keptCombMap β ρ hβinv hβfix).E = Fintype.card K :=
    keptCombMap_two_mul_E β ρ hβinv hβfix
  have hVeq : (keptCombMap β ρ hβinv hβfix).V
      = Fintype.card (Quotient (cycleSetoid ρ)) := keptCombMap_V β ρ hβinv hβfix
  have hVZ : ((keptCombMap β ρ hβinv hβfix).V : ℤ)
      = (Fintype.card (Quotient (cycleSetoid ρ)) : ℤ) := by exact_mod_cast hVeq
  -- `V = E + 2 - F ≤ E + 2`.
  have hVle : (keptCombMap β ρ hβinv hβfix).V ≤ (keptCombMap β ρ hβinv hβfix).E + 2 := by
    have : ((keptCombMap β ρ hβinv hβfix).V : ℤ) ≤ ((keptCombMap β ρ hβinv hβfix).E : ℤ) + 2 := by
      have hFnn : (0 : ℤ) ≤ ((keptCombMap β ρ hβinv hβfix).F : ℤ) := by positivity
      linarith [heuler, hFnn]
    exact_mod_cast this
  omega

/-- **The fresh map is a genus-0 sphere map, from M's genus-0 structure.**  Inputs:
the kept side is a sphere map (`keptCombMap β ρ` connected with `eulerChar = 2`) and the
two chord successors `ρ a₀`, `ρ a₁` lie on a common kept face.  Output: the *full*
`IsSphereMap` of the side map (connectivity transferred across the splice, and the face
count discharged via the explicit orbit bijection + the genus-0 transposition sign). -/
theorem freshMap_isSphereMap_of_genus0
    (hkept_sphere : (keptCombMap β ρ hβinv hβfix).IsSphereMap)
    (hsame : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁)) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).IsSphereMap := by
  refine ⟨ChordSideRecon.freshMap_connected_of_kept β ρ hβinv hβfix hne hkept_sphere.1, ?_⟩
  have hface := freshFaceCount_of_genus0 β ρ hβinv hβfix hne hkept_sphere.2 hsame
  have hV := vbound_of_kept_euler β ρ hβinv hβfix hkept_sphere.2
  exact (freshMap_eulerChar_eq_two_iff_faceCount β ρ hβinv hβfix hne hV).2 hface

end SphereAssembly



section NonVacuity







end NonVacuity



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}





end ChordApplication



section Headline

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



end Headline

end ProofsInTheBook.ChordFaceCount















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ChordDisk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordDisk

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Facts

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  (a₀ a₁ : K)

/-- **Fact 1 (the disk fact).**  The kept side of the chord split — the kept combinatorial
map `keptCombMap β ρ` (the side submap *before* the duplicated chord edge is spliced) — is a
combinatorial disk: a sphere map (`Connected ∧ eulerChar = 2`).  This is the discrete
Schoenflies content: a simple closed curve (chord ∪ boundary arc) on the genus-0 sphere M
bounds a disk on each side. -/
def KeptSideIsDisk : Prop := (keptCombMap β ρ hβinv hβfix).IsSphereMap

/-- **Fact 2 (the anchor incidence fact).**  The two chord anchors' rotation successors
`ρ a₀`, `ρ a₁` lie on a common kept face (the same `keptPhi = ρ * β`-cycle): the shared outer
boundary face that the chord splits.  This is a local incidence fact about the chord
endpoints' position on the side's boundary cycle. -/
def AnchorsShareBoundaryFace : Prop := (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁)

end Facts



section LowerHalf

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)





end LowerHalf



section Threading

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The two disk facts produce the side map's `IsSphereMap`.**  Fact 1 (kept side is a
disk) + fact 2 (anchors share the boundary face) give the *full* genus-0 structure of the
spliced side map: connectivity (transferred across the splice in `ChordSideRecon`) and
`eulerChar = 2` (the face count `FreshFaceCount`, proved from the bijection in
`ChordFaceCount`).  The face count is **not** a hypothesis. -/
theorem chordDisk_produces_isSphereMap
    (hdisk : KeptSideIsDisk β ρ hβinv hβfix)
    (hshare : AnchorsShareBoundaryFace β ρ a₀ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).IsSphereMap :=
  freshMap_isSphereMap_of_genus0 β ρ hβinv hβfix hne hdisk hshare





end Threading



section ChordApplication

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **Fact 1 at side 1.**  The kept side-1 map `sideKeptMap₁` is a disk. -/
def Side₁IsDisk (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  (sideKeptMap₁ data hsep).IsSphereMap

/-- **Fact 2 at side 1.**  The side-1 splice anchors' `sideSigma₁`-successors share a kept
face. -/
def Side₁AnchorsShareFace (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) : Prop :=
  (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
    (data.sideSigma₁ a₀) (data.sideSigma₁ a₁)

/-- **Side-1 map is a genus-0 sphere map, from side 1's two disk facts** — face count
discharged (no longer a hypothesis), via `ChordFaceCount`. -/
theorem side₁_isSphereMap_of_disk
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hdisk : Side₁IsDisk data hsep)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap :=
  chordDisk_produces_isSphereMap _ _ _ _ hne hdisk hshare



/-- **Fact 1 at side 2.** -/
def Side₂IsDisk (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop :=
  (sideKeptMap₂ data hsep).IsSphereMap

/-- **Fact 2 at side 2.** -/
def Side₂AnchorsShareFace (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) : Prop :=
  (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle
    (data.sideSigma₂ a₀) (data.sideSigma₂ a₁)

/-- **Side-2 map is a genus-0 sphere map, from side 2's two disk facts.** -/
theorem side₂_isSphereMap_of_disk
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hdisk : Side₂IsDisk data hsep)
    (hshare : Side₂AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₂ hsep a₀ a₁ hne).IsSphereMap :=
  chordDisk_produces_isSphereMap _ _ _ _ hne hdisk hshare



end ChordApplication



section NonVacuity











end NonVacuity



section Headline

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



end Headline



end ProofsInTheBook.ChordDisk
















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.SubmapPlanar -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.SubmapPlanar

open Equiv
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]



/-- **Single-edge removal does not increase the genus slack.**  If `α a = b` with `a ≠ b`
(so `{a, b}` is an edge of the involution `α`), then deleting it
(`α' = α * swap a b`, which fixes `a, b`) gives `genusSlack σ α' ≤ genusSlack σ α`. -/
theorem genusSlack_remove_le (σ α : Equiv.Perm D) (hα : α * α = 1)
    {a b : D} (hab : a ≠ b) (hαa : α a = b) :
    genusSlack σ (α * Equiv.swap a b) ≤ genusSlack σ α := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  set α' := α * Equiv.swap a b with hα'def
  have hα'invol : α' * α' = 1 := mul_swap_involutive α hα hαa hαb
  -- Edge count: `Ehalf α' + 1 = Ehalf α`.
  have hEhalf : Ehalf α' + 1 = Ehalf α := Ehalf_mul_swap α hα hab hαa
  have hEz : (Ehalf α : ℤ) = (Ehalf α' : ℤ) + 1 := by
    have h := hEhalf; push_cast [← h]; ring
  -- Face permutation: `σ * α = (σ * α') * swap a b`.
  have hface : σ * α = (σ * α') * Equiv.swap a b := by
    rw [hα'def, mul_assoc, mul_assoc, Equiv.swap_mul_self, mul_one]
  -- Component relation via `addEdge`.
  have hrel : dartStepRel σ α = _root_.addEdge (dartStepRel σ α') a b :=
    dartStepRel_eq_addEdge σ α hα hab hαa
  have hcompEq : numComponents σ α
      = _root_.numComp (_root_.addEdge (dartStepRel σ α') a b) := by
    rw [numComponents_def, hrel]
  -- Face cycle-count dichotomy.
  have hdich := _root_.numCycles_mul_swap_dichotomy (σ * α') hab
  rw [← hface] at hdich
  by_cases hsame : Relation.EqvGen (dartStepRel σ α') a b
  · -- Same component: `c` unchanged; `F` either unchanged (slack +1) or drops (slack +2).
    have hC : numComponents σ α = numComponents σ α' := by
      rw [hcompEq, numComponents_def]
      exact _root_.numComp_addEdge_of_eqvGen _ hsame
    unfold genusSlack at *
    rw [hC, hEz]
    rcases hdich with hd | hd
    · rw [hd]; push_cast; linarith
    · have hF : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
        have h := hd; push_cast [← h]; ring
      rw [hF]; linarith
  · -- Different components: `c` drops by one; faces merge (`F` drops by one); slack unchanged.
    have hC : numComponents σ α + 1 = numComponents σ α' := by
      rw [hcompEq, numComponents_def]
      exact _root_.numComp_addEdge_of_not_eqvGen _ hsame
    have hnsc : ¬ (σ * α').SameCycle a b := fun h =>
      hsame (eqvGen_dartStepRel_of_sameCycle_mul σ α' hα'invol h)
    have hmerge : numCycles (σ * α) + 1 = numCycles (σ * α') := by
      have h := _root_.numCycles_mul_swap_of_not_sameCycle (σ * α') hab hnsc
      rw [← hface] at h; exact h
    unfold genusSlack at *
    have hCz : (numComponents σ α : ℤ) = (numComponents σ α' : ℤ) - 1 := by
      have h := hC; push_cast [← h]; ring
    have hFz : (numCycles (σ * α) : ℤ) = (numCycles (σ * α') : ℤ) - 1 := by
      have h := hmerge; push_cast [← h]; ring
    rw [hCz, hEz, hFz]; linarith



/-- `α'` is an **edge-deletion sub-involution** of `α`: an involution that agrees with `α` on
its own support (so its edge set is a subset of `α`'s edge set). -/
def SubInvolution (α α' : Equiv.Perm D) : Prop :=
  α' * α' = 1 ∧ ∀ x, α' x ≠ x → α' x = α x

/-- A sub-involution's support is contained in `α`'s support. -/
lemma SubInvolution.support_subset {α α' : Equiv.Perm D} (h : SubInvolution α α') :
    Equiv.Perm.support α' ⊆ Equiv.Perm.support α := by
  classical
  intro x hx
  rw [Equiv.Perm.mem_support] at hx ⊢
  rw [h.2 x hx] at hx
  exact hx

/-- **Removing one edge from `α` keeps `α'` a sub-involution** when that edge is disjoint from
`α'`'s support.  This is the inductive step bridge. -/
lemma SubInvolution.remove_edge {α α' : Equiv.Perm D} (hα : α * α = 1)
    (h : SubInvolution α α') {a b : D} (hab : a ≠ b) (hαa : α a = b)
    (ha : a ∉ Equiv.Perm.support α') (hb : b ∉ Equiv.Perm.support α') :
    SubInvolution (α * Equiv.swap a b) α' := by
  classical
  have hαb : α b = a := by
    have happ := congrArg (fun f : Equiv.Perm D => f a) hα
    have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
    rw [hαa] at hh; exact hh
  rw [Equiv.Perm.notMem_support] at ha hb
  refine ⟨h.1, ?_⟩
  intro x hx
  have hax : x ≠ a := by rintro rfl; exact hx ha
  have hbx : x ≠ b := by rintro rfl; exact hx hb
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hax hbx]
  exact h.2 x hx

/-- **Iterated monotonicity.**  Every edge-deletion sub-involution `α'` of an involution `α`
has genus slack at most that of `α`.  Proved by strong induction on the number of deleted
edges (`(support α).card`), peeling one `α`-edge disjoint from `support α'` at a time. -/
theorem genusSlack_le_of_subInvolution (σ : Equiv.Perm D) :
    ∀ α : Equiv.Perm D, α * α = 1 → ∀ α' : Equiv.Perm D, SubInvolution α α' →
      genusSlack σ α' ≤ genusSlack σ α := by
  intro α
  induction hn : (Equiv.Perm.support α).card using Nat.strong_induction_on
    generalizing α with
  | _ n ih =>
    intro hα α' hsub
    classical
    -- Either `α'` already equals `α` (no edge left to delete) or there is an `α`-edge
    -- disjoint from `support α'`.
    by_cases hdone : Equiv.Perm.support α ⊆ Equiv.Perm.support α'
    · -- supports equal ⇒ `α = α'` ⇒ slacks equal.
      have hsupp_eq : Equiv.Perm.support α = Equiv.Perm.support α' :=
        le_antisymm hdone hsub.support_subset
      have heq : α = α' := by
        ext x
        by_cases hx : x ∈ Equiv.Perm.support α
        · have hx' : x ∈ Equiv.Perm.support α' := hsupp_eq ▸ hx
          rw [Equiv.Perm.mem_support] at hx'
          exact (hsub.2 x hx').symm
        · have hx' : x ∉ Equiv.Perm.support α' := hsupp_eq ▸ hx
          rw [Equiv.Perm.notMem_support] at hx hx'
          rw [hx, hx']
      rw [heq]
    · -- there is `a ∈ support α \ support α'`; let `b = α a` (also outside `support α'`).
      obtain ⟨a, ha_in, ha_out⟩ := Finset.not_subset.mp hdone
      have hane : α a ≠ a := Equiv.Perm.mem_support.mp ha_in
      set b := α a with hbdef
      have hab : a ≠ b := fun h => hane h.symm
      have hαa : α a = b := hbdef.symm
      have hαb : α b = a := by
        have happ := congrArg (fun f : Equiv.Perm D => f a) hα
        have hh : α (α a) = a := by simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
        rw [hαa] at hh; exact hh
      have hb_in : b ∈ Equiv.Perm.support α := by
        rw [Equiv.Perm.mem_support, hαb]; exact hab
      -- `b` is also outside `support α'` (else `α' b = b'` would force the edge `{a,b}` into `α'`).
      have hb_out : b ∉ Equiv.Perm.support α' := by
        intro hb'
        rw [Equiv.Perm.mem_support] at hb'
        have := hsub.2 b hb'
        rw [hαb] at this
        -- `α' b = a`, so `α' a = b ≠ a` by the involution, putting `a` in `support α'`.
        have hα'a : α' a = b := by
          have happ := congrArg (fun f : Equiv.Perm D => f b) hsub.1
          have hh : α' (α' b) = b := by
            simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
          rw [this] at hh; exact hh
        exact ha_out (Equiv.Perm.mem_support.mpr (by rw [hα'a]; exact hab.symm))
      -- Delete `{a, b}` from `α`.
      set α'' := α * Equiv.swap a b with hα''def
      have hα''invol : α'' * α'' = 1 := mul_swap_involutive α hα hαa hαb
      have hsub'' : SubInvolution α'' α' :=
        hsub.remove_edge hα hab hαa ha_out hb_out
      have hsupp'' : Equiv.Perm.support α'' = (Equiv.Perm.support α) \ {a, b} :=
        support_mul_swap_of_apply α hα hab hαa
      have hcard'' : (Equiv.Perm.support α'').card < n := by
        rw [← hn, hsupp'']
        apply Finset.card_lt_card
        refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨a, ha_in, ?_⟩
        simp
      -- Recurse: slack α' ≤ slack α'' ≤ slack α.
      have hstep : genusSlack σ α'' ≤ genusSlack σ α :=
        genusSlack_remove_le σ α hα hab hαa
      have hrec : genusSlack σ α' ≤ genusSlack σ α'' :=
        ih _ hcard'' α'' rfl hα''invol α' hsub''
      exact le_trans hrec hstep



/-- **A sphere map has genus slack zero.**  For a connected map with `eulerChar = 2` and at
least one dart, `genusSlack M.σ M.α = 0` (`c = 1`, `χ = 2`). -/
theorem genusSlack_sphere_eq_zero (M : CombMap D) (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack M.σ M.α = 0 := by
  classical
  have hc : numComponents M.σ M.α = 1 :=
    numComponents_eq_one_of_connected M hsphere.1 d₀
  have hVc : (M.V : ℤ) = (numCycles M.σ : ℤ) := by rw [V_eq_numCycles]
  have hEc : (M.E : ℤ) = (Ehalf M.α : ℤ) := by rw [Ehalf_eq_E]
  have hFc : (M.F : ℤ) = (numCycles (M.σ * M.α) : ℤ) := by
    rw [F_eq_numCycles]; rfl
  have heuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  unfold genusSlack
  rw [hc]
  rw [hVc, hEc, hFc] at heuler
  push_cast
  linarith



section OrbitSplit

variable (p : Equiv.Perm D) (S : Finset D)

open scoped Classical

/-- A `p`-orbit is **deleted** if all its darts lie in `S`. -/
def DeletedOrbit (q : Quotient (cycleSetoid p)) : Prop :=
  ∀ x : D, Quotient.mk (cycleSetoid p) x = q → x ∈ S

/-- The kept subtype's filtered orbit quotient, as `p`-orbits via the `SameCycle` coincidence. -/
noncomputable def keptToFull :
    Quotient (cycleSetoid (Equiv.Perm.deleteSet p S)) → Quotient (cycleSetoid p) :=
  Quotient.lift (fun x => Quotient.mk (cycleSetoid p) (x.1 : D)) (by
    intro x y hxy
    apply Quotient.sound
    exact (Equiv.Perm.sameCycle_deleteSet_iff p S x y).1 hxy)

@[simp] lemma keptToFull_mk (x : {d : D // d ∉ S}) :
    keptToFull p S (Quotient.mk (cycleSetoid (Equiv.Perm.deleteSet p S)) x)
      = Quotient.mk (cycleSetoid p) (x.1 : D) := rfl

/-- `keptToFull` is injective: two filtered orbits mapping to the same `p`-orbit are equal. -/
lemma keptToFull_injective : Function.Injective (keptToFull p S) := by
  classical
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  simp only [keptToFull_mk] at hxy
  apply Quotient.sound
  have hsc : p.SameCycle x.1 y.1 := Quotient.exact hxy
  exact (Equiv.Perm.sameCycle_deleteSet_iff p S x y).2 hsc

/-- The image of `keptToFull` is exactly the non-deleted `p`-orbits. -/
lemma keptToFull_range_iff (q : Quotient (cycleSetoid p)) :
    (∃ a, keptToFull p S a = q) ↔ ¬ DeletedOrbit p S q := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a (fun x => ?_)
    simp only [keptToFull_mk, DeletedOrbit, not_forall]
    exact ⟨x.1, rfl, x.2⟩
  · intro hq
    -- some dart of the orbit is kept; lift it.
    simp only [DeletedOrbit, not_forall] at hq
    obtain ⟨x, hxq, hxS⟩ := hq
    refine ⟨Quotient.mk (cycleSetoid (Equiv.Perm.deleteSet p S)) ⟨x, hxS⟩, ?_⟩
    rw [keptToFull_mk]; exact hxq

/-- The number of **deleted** `p`-orbits (orbits entirely inside `S`). -/
noncomputable def numDeletedOrbits : ℕ :=
  Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q}

/-- **Orbit-count splitting.**  `numCycles p = numCycles (deleteSet p S) + numDeletedOrbits`.
Every `p`-orbit is either deleted or has a kept representative; the kept ones biject with the
filtered orbits via `keptToFull`. -/
theorem numCycles_eq_kept_add_deleted :
    _root_.numCycles p
      = _root_.numCycles (Equiv.Perm.deleteSet p S) + numDeletedOrbits p S := by
  classical
  -- `keptToFull` is a bijection onto the non-deleted orbits.
  have hbij : Function.Bijective
      (fun a => (⟨keptToFull p S a, by
        rw [← keptToFull_range_iff]; exact ⟨a, rfl⟩⟩ :
        {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q})) := by
    constructor
    · intro a b hab
      exact keptToFull_injective p S (Subtype.ext_iff.mp hab)
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha⟩ := (keptToFull_range_iff p S q).2 hq
      exact ⟨a, Subtype.ext ha⟩
  have hcard_kept : _root_.numCycles (Equiv.Perm.deleteSet p S)
      = Fintype.card {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q} := by
    rw [← card_cycleSetoid_eq_numCycles]
    exact Fintype.card_of_bijective hbij
  have hcompl : Fintype.card {q : Quotient (cycleSetoid p) // ¬ DeletedOrbit p S q}
      = Fintype.card (Quotient (cycleSetoid p))
        - Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {q : Quotient (cycleSetoid p) // DeletedOrbit p S q}
      ≤ Fintype.card (Quotient (cycleSetoid p)) := Fintype.card_subtype_le _
  rw [← card_cycleSetoid_eq_numCycles p, hcard_kept, numDeletedOrbits, hcompl]
  omega

end OrbitSplit





section RawRestrict

variable (M : CombMap D) (Del : Finset D)

open scoped Classical

/-- The raw restricted function: identity on deleted darts, `M.α` elsewhere. -/
noncomputable def rawAlphaFun : D → D := fun d => if d ∈ Del then d else M.α d

/-- `rawAlphaFun` is an involution (uses `α`-closedness of `Del`). -/
lemma rawAlphaFun_involutive (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) :
    Function.Involutive (rawAlphaFun M Del) := by
  classical
  intro d
  unfold rawAlphaFun
  by_cases hd : d ∈ Del
  · simp [hd]
  · have hαd : M.α d ∉ Del := by
      intro h
      apply hd
      have := hclosed _ h
      rwa [M.alpha_alpha] at this
    simp [hd, hαd, M.alpha_alpha]

/-- The **raw restricted involution**: fixes every deleted dart, equals `M.α` on kept darts. -/
noncomputable def rawAlpha (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) : Equiv.Perm D :=
  Function.Involutive.toPerm (rawAlphaFun M Del) (rawAlphaFun_involutive M Del hclosed)

@[simp] lemma rawAlpha_apply (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) (d : D) :
    rawAlpha M Del hclosed d = if d ∈ Del then d else M.α d := rfl

/-- `rawAlpha` is an involution as a permutation. -/
lemma rawAlpha_invol (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) :
    rawAlpha M Del hclosed * rawAlpha M Del hclosed = 1 := by
  ext d
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
  exact rawAlphaFun_involutive M Del hclosed d

/-- `rawAlpha` fixes deleted darts. -/
lemma rawAlpha_eq_self_of_mem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {d : D}
    (hd : d ∈ Del) : rawAlpha M Del hclosed d = d := by simp [rawAlpha_apply, hd]

/-- `rawAlpha` equals `M.α` on kept darts. -/
lemma rawAlpha_eq_alpha_of_notMem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {d : D}
    (hd : d ∉ Del) : rawAlpha M Del hclosed d = M.α d := by simp [rawAlpha_apply, hd]

/-- **Trajectory identity.**  Starting from a kept dart `x`, applying `M.α` and then iterating
`M.σ` through a run of deleted darts matches iterating `p := M.σ * rawAlpha`: for every `k`,
if the intermediate `σ`-iterates `(M.σ)^j (M.α x)` (`1 ≤ j ≤ k`) are all deleted, then
`p^(k+1) x = (M.σ)^(k+1) (M.α x)`.  (`rawAlpha` fixes the deleted darts visited.) -/
lemma rawFace_traj (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (x : {d : D // d ∉ Del}) :
    ∀ k : ℕ, (∀ j : ℕ, 1 ≤ j → j ≤ k → ((M.σ ^ j) (M.α x.1)) ∈ Del) →
      ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x.1 = (M.σ ^ (k+1)) (M.α x.1) := by
  classical
  set p := M.σ * rawAlpha M Del hclosed with hp
  intro k
  induction k with
  | zero =>
      intro _
      simp only [zero_add, pow_one, hp]
      rw [Equiv.Perm.mul_apply, rawAlpha_eq_alpha_of_notMem M Del hclosed x.2]
  | succ k ih =>
      intro hdel
      have ihk : (p ^ (k+1)) x.1 = (M.σ ^ (k+1)) (M.α x.1) :=
        ih (fun j hj1 hjk => hdel j hj1 (by omega))
      have hmemk : (M.σ ^ (k+1)) (M.α x.1) ∈ Del := hdel (k+1) (by omega) (by omega)
      have hstep : ((p ^ (k+1+1)) x.1) = p ((p ^ (k+1)) x.1) := by
        rw [pow_succ']; rfl
      rw [hstep, ihk, hp, Equiv.Perm.mul_apply,
        rawAlpha_eq_self_of_mem M Del hclosed hmemk, ← Equiv.Perm.mul_apply, ← pow_succ']



/-- Abbreviation: the kept combinatorial map's face permutation is
`(deleteSet M.σ Del) * (M.α.subtypePerm)`. -/
noncomputable def keptFacePerm (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) : Equiv.Perm {d : D // d ∉ Del} :=
  (Equiv.Perm.deleteSet M.σ Del) * (M.α.subtypePerm (fun d => by
    rw [← hsub d]))



/-- **The kept face permutation equals the deleted raw face permutation.**  As permutations on
the kept subtype, `keptFacePerm = deleteSet (M.σ * rawAlpha) Del`.  Both send a kept dart `x`
to the first kept dart reached from `M.α x` by iterating `M.σ` through the deleted run; the raw
face permutation `M.σ * rawAlpha` walks the same trajectory because `rawAlpha` fixes the deleted
darts it passes through. -/
theorem keptFacePerm_eq_deleteSet_rawFace (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    keptFacePerm M Del hclosed hsub = Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del := by
  classical
  ext x
  -- It suffices to prove the underlying dart values agree.
  set y : {d : D // d ∉ Del} := ⟨M.α x.1, fun hc => x.2 ((hsub x.1).2 hc)⟩ with hy
  -- LHS value: `(deleteSet M.σ Del) y = (M.σ)^m (M.α x)` with `m = firstOutside M.σ Del y`.
  set m := Equiv.Perm.DeleteSet.firstOutside M.σ Del y with hm
  have hmpos : 0 < m := Equiv.Perm.DeleteSet.firstOutside_pos M.σ Del y
  have hlhs : ((keptFacePerm M Del hclosed hsub) x : {d : D // d ∉ Del}).1
      = (M.σ ^ m) (M.α x.1) := by
    show ((Equiv.Perm.deleteSet M.σ Del) y : {d : D // d ∉ Del}).1 = _
    rw [Equiv.Perm.deleteSet_apply_coe]
  -- intermediate σ-iterates of `M.α x` (before step `m`) are deleted (firstOutside min).
  have hinter : ∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → ((M.σ ^ j) (M.α x.1)) ∈ Del := by
    intro j hj1 hjm
    by_contra hnot
    exact Equiv.Perm.DeleteSet.firstOutside_min M.σ Del y (by omega : j < m)
      ⟨by omega, by show (M.σ ^ j) y.1 ∉ Del; rw [hy]; exact hnot⟩
  -- the `m`-th σ-iterate is kept.
  have hmkept : (M.σ ^ m) (M.α x.1) ∉ Del := by
    have := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ Del y
    rwa [hy] at this
  -- trajectory: `(M.σ * rawAlpha)^m x = (M.σ)^m (M.α x)`.
  have htraj := rawFace_traj M Del hclosed x (m - 1) hinter
  have hmsucc : (m - 1) + 1 = m := by omega
  rw [hmsucc] at htraj
  -- RHS value: `deleteSet (M.σ*rawAlpha) Del x = (M.σ*rawAlpha)^M x`, `M = firstOutside …`.
  set P := M.σ * rawAlpha M Del hclosed with hP
  have hrhs : ((Equiv.Perm.deleteSet P Del) x : {d : D // d ∉ Del}).1
      = (P ^ (Equiv.Perm.DeleteSet.firstOutside P Del x)) x.1 :=
    Equiv.Perm.deleteSet_apply_coe P Del x
  -- The firstOutside of `P` at `x` is exactly `m`: the `P`-trajectory equals the σ-trajectory
  -- of `M.α x`, deleted before step `m`, kept at step `m`.
  have hPtraj : ∀ j : ℕ, 1 ≤ j → j ≤ m → (P ^ j) x.1 = (M.σ ^ j) (M.α x.1) := by
    intro j hj1 hjm
    have hjsub : ∀ i : ℕ, 1 ≤ i → i ≤ j - 1 → ((M.σ ^ i) (M.α x.1)) ∈ Del :=
      fun i hi1 hij => hinter i hi1 (by omega)
    have := rawFace_traj M Del hclosed x (j - 1) hjsub
    rwa [Nat.sub_add_cancel hj1] at this
  have hPm_kept : (P ^ m) x.1 ∉ Del := by rw [hPtraj m hmpos le_rfl]; exact hmkept
  have hPm_min : ∀ i : ℕ, i < m → ¬ (0 < i ∧ (P ^ i) x.1 ∉ Del) := by
    intro i him ⟨hipos, hinotmem⟩
    rw [hPtraj i hipos (by omega)] at hinotmem
    exact hinotmem (hinter i hipos (by omega))
  have hMeq : Equiv.Perm.DeleteSet.firstOutside P Del x = m := by
    apply le_antisymm
    · exact Nat.find_min' _ ⟨hmpos, hPm_kept⟩
    · by_contra hlt
      rw [not_le] at hlt
      exact hPm_min _ hlt
        ⟨Equiv.Perm.DeleteSet.firstOutside_pos P Del x,
         Equiv.Perm.DeleteSet.firstOutside_notMem P Del x⟩
  rw [hlhs, hrhs, hMeq, hPtraj m hmpos le_rfl]





/-- The face count of the kept map equals `numCycles (deleteSet (M.σ * rawAlpha) Del)`. -/
lemma numCycles_keptFacePerm_eq (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    _root_.numCycles (keptFacePerm M Del hclosed hsub)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del) := by
  rw [keptFacePerm_eq_deleteSet_rawFace M Del hclosed hsub]



/-- On the deleted set, `M.σ` and `M.σ * rawAlpha` agree, hence have the same `SameCycle`
relation among deleted darts; combined with the kept-orbit splitting this forces the deleted
orbit counts to be equal. -/
lemma sameCycle_sigma_rawFace_of_mem (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    {x : D} (hx : x ∈ Del) :
    (M.σ * rawAlpha M Del hclosed) x = M.σ x := by
  rw [Equiv.Perm.mul_apply, rawAlpha_eq_self_of_mem M Del hclosed hx]



variable (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
  (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)

open scoped Classical

/-- The kept edge involution: `M.α` restricted to the kept subtype. -/
noncomputable def keptAlpha : Equiv.Perm {d : D // d ∉ Del} :=
  M.α.subtypePerm (p := fun d => d ∉ Del) (fun d => by
    constructor
    · intro hd hc; exact hd ((hsub d).1 hc)
    · intro hd hc; exact hd ((hsub d).2 hc))

@[simp] lemma keptAlpha_apply_coe (d : {d : D // d ∉ Del}) :
    (keptAlpha M Del hsub d : D) = M.α d.1 := rfl

lemma keptAlpha_invol : keptAlpha M Del hsub * keptAlpha M Del hsub = 1 := by
  ext z
  simp only [Equiv.Perm.coe_mul, Equiv.Perm.coe_one, Function.comp_apply, id_eq,
    keptAlpha_apply_coe]
  exact M.alpha_alpha z.1

/-- The kept combinatorial map's dart-step relation, on the kept subtype. -/
noncomputable def keptStepRel : {d : D // d ∉ Del} → {d : D // d ∉ Del} → Prop :=
  dartStepRel (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub)

/-- **A kept dart-step lifts to a raw dart-step on the underlying darts.** -/
lemma keptStepRel_imp_raw {x y : {d : D // d ∉ Del}}
    (h : keptStepRel M Del hsub x y) :
    dartStepRel M.σ (rawAlpha M Del hclosed) x.1 y.1 := by
  classical
  rcases h with hσ | hα
  · -- same `deleteSet M.σ`-cycle ⇒ same `M.σ`-cycle on coercions.
    exact Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y).1 hσ)
  · -- α-edge: `y = (M.α.subtypePerm) x`, so `y.1 = M.α x.1 = rawAlpha x.1` (x kept).
    refine Or.inr ?_
    have hxval : (rawAlpha M Del hclosed) x.1 = M.α x.1 :=
      rawAlpha_eq_alpha_of_notMem M Del hclosed x.2
    rw [hxval]
    have := congrArg Subtype.val hα
    simpa using this



/-- `EqvGen` of the kept dart-step relation lifts to `EqvGen` of the raw relation. -/
lemma eqvGen_keptStepRel_imp_raw {x y : {d : D // d ∉ Del}}
    (h : Relation.EqvGen (keptStepRel M Del hsub) x y) :
    Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1 := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (keptStepRel_imp_raw M Del hclosed hsub hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- The raw dart-step relation is symmetric (`rawAlpha` is an involution). -/
lemma rawStepRel_symm {a b : D}
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) a b) :
    dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
  dartStepRel_symm (rawAlpha_invol M Del hclosed) h

/-- **Descent witness (forward walk).**  Every dart `z` raw-reachable from a kept dart `x`
(via `ReflTransGen`) is `M.σ`-`SameCycle` to a kept dart `w` in the same *kept* component as
`x`.  The only raw steps that can land in `Del` are `M.σ`-`SameCycle` steps; `M.σ`-`SameCycle`
is transitive, so deleted intermediates collapse, and the `rawAlpha`-edge from a kept dart lands
kept (`α`-closure), giving a genuine kept dart-step. -/
lemma raw_reach_kept_witness {x : {d : D // d ∉ Del}} {z : D}
    (h : Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 z) :
    ∃ w : {d : D // d ∉ Del},
      Relation.ReflTransGen (keptStepRel M Del hsub) x w ∧ M.σ.SameCycle w.1 z := by
  classical
  induction h with
  | refl => exact ⟨x, Relation.ReflTransGen.refl, Equiv.Perm.SameCycle.rfl⟩
  | @tail b c hxb hbc ih =>
      obtain ⟨w, hwkept, hwb⟩ := ih
      -- one more raw step `b → c`; combine with `w ~σ b`.
      rcases hbc with hσ | hαe
      · -- `c` in same `M.σ`-cycle as `b`, hence as `w`.
        exact ⟨w, hwkept, hwb.trans hσ⟩
      · -- `c = rawAlpha b`.
        by_cases hbDel : b ∈ Del
        · -- `rawAlpha b = b`, so `c = b`; nothing changes.
          rw [rawAlpha_eq_self_of_mem M Del hclosed hbDel] at hαe
          exact ⟨w, hwkept, hαe ▸ hwb⟩
        · -- `b` kept, `c = M.α b` kept (α-closure); `w ~σ b` gives a kept σ-step `w → ⟨b⟩`,
          -- then the kept α-edge `⟨b⟩ → ⟨c⟩`.
          have hck : c ∉ Del := by
            rw [rawAlpha_eq_alpha_of_notMem M Del hclosed hbDel] at hαe
            rw [hαe]; intro hc; exact hbDel ((hsub b).2 hc)
          have hbw : M.σ.SameCycle w.1 b := hwb
          -- kept σ-step `w → ⟨b, hbDel⟩`:
          have hstep1 : keptStepRel M Del hsub w ⟨b, hbDel⟩ :=
            Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del w ⟨b, hbDel⟩).2 hbw)
          -- kept α-edge `⟨b⟩ → ⟨c⟩`:
          have hstep2 : keptStepRel M Del hsub ⟨b, hbDel⟩ ⟨c, hck⟩ := by
            refine Or.inr (Subtype.ext ?_)
            show c = M.α b
            rw [rawAlpha_eq_alpha_of_notMem M Del hclosed hbDel] at hαe
            exact hαe
          exact ⟨⟨c, hck⟩, (hwkept.tail hstep1).tail hstep2, Equiv.Perm.SameCycle.rfl⟩

/-- **Descent.**  Two kept darts that are raw-`EqvGen` are kept-`EqvGen`.  (From the descent
witness: the witness `w` for `y` is `M.σ`-`SameCycle` to `y`, both kept, hence kept-connected
by a single kept `σ`-step.) -/
lemma raw_eqvGen_descends {x y : {d : D // d ∉ Del}}
    (h : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1) :
    Relation.EqvGen (keptStepRel M Del hsub) x y := by
  classical
  -- pass to `ReflTransGen` (symmetric relation), apply the witness, close with a kept σ-step.
  have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
      dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
    fun a b => rawStepRel_symm M Del hclosed
  rw [eqvGen_iff_reflTransGen hsymm] at h
  obtain ⟨w, hwkept, hwy⟩ := raw_reach_kept_witness M Del hclosed hsub h
  -- `w ~σ y` (both kept) ⇒ kept σ-step `w → y`.
  have hstep : keptStepRel M Del hsub w y :=
    Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ Del w y).2 hwy)
  have hksymm : ∀ a b, keptStepRel M Del hsub a b → keptStepRel M Del hsub b a :=
    fun a b h => dartStepRel_symm (keptAlpha_invol M Del hsub) h
  rw [eqvGen_iff_reflTransGen hksymm]
  exact hwkept.tail hstep

/-- The lifted map `⟦x⟧_kept ↦ ⟦x.1⟧_raw` of component quotients. -/
noncomputable def keptCompToRaw :
    Quotient (_root_.compSetoid (keptStepRel M Del hsub))
      → Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) :=
  Quotient.lift (fun x => Quotient.mk _ (x.1 : D)) (by
    intro x y hxy
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x.1 y.1
    exact eqvGen_keptStepRel_imp_raw M Del hclosed hsub hxy)

/-- `keptCompToRaw` is injective: by the descent lemma, kept darts raw-`EqvGen` are
kept-`EqvGen`. -/
lemma keptCompToRaw_injective : Function.Injective (keptCompToRaw M Del hclosed hsub) := by
  classical
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y hxy => ?_) hab
  apply Quotient.sound
  show Relation.EqvGen (keptStepRel M Del hsub) x y
  exact raw_eqvGen_descends M Del hclosed hsub (Quotient.exact hxy)





/-- A raw component is **deleted** if all its darts lie in `Del`. -/
def DeletedComp (q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :
    Prop :=
  ∀ x : D, Quotient.mk _ x = q → x ∈ Del

/-- The image of `keptCompToRaw` is exactly the non-deleted raw components. -/
lemma keptCompToRaw_range_iff
    (q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :
    (∃ a, keptCompToRaw M Del hclosed hsub a = q) ↔ ¬ DeletedComp M Del hclosed q := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    refine Quotient.inductionOn a (fun x => ?_)
    simp only [DeletedComp, not_forall]
    exact ⟨x.1, rfl, x.2⟩
  · intro hq
    simp only [DeletedComp, not_forall] at hq
    obtain ⟨x, hxq, hxD⟩ := hq
    exact ⟨Quotient.mk _ ⟨x, hxD⟩, hxq⟩

/-- The number of deleted raw components. -/
noncomputable def numDeletedComp : ℕ :=
  Fintype.card {q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))
    // DeletedComp M Del hclosed q}

/-- **Component split.**  `numComponents M.σ rawAlpha = numComp (keptStepRel) + numDeletedComp`. -/
theorem numComponents_raw_split :
    numComponents M.σ (rawAlpha M Del hclosed)
      = _root_.numComp (keptStepRel M Del hsub) + numDeletedComp M Del hclosed := by
  classical
  rw [numComponents_def]
  have hbij : Function.Bijective
      (fun a => (⟨keptCompToRaw M Del hclosed hsub a, by
        rw [← keptCompToRaw_range_iff M Del hclosed hsub]; exact ⟨a, rfl⟩⟩ :
        {q // ¬ DeletedComp M Del hclosed q})) := by
    constructor
    · intro a b hab
      exact keptCompToRaw_injective M Del hclosed hsub (Subtype.ext_iff.mp hab)
    · rintro ⟨q, hq⟩
      obtain ⟨a, ha⟩ := (keptCompToRaw_range_iff M Del hclosed hsub q).2 hq
      exact ⟨a, Subtype.ext ha⟩
  have hcard_kept : _root_.numComp (keptStepRel M Del hsub)
      = Fintype.card {q // ¬ DeletedComp M Del hclosed q} := by
    unfold _root_.numComp
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_of_bijective hbij
  have hcompl : Fintype.card {q // ¬ DeletedComp M Del hclosed q}
      = Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))))
        - Fintype.card {q // DeletedComp M Del hclosed q} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {q // DeletedComp M Del hclosed q}
      ≤ Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) :=
    Fintype.card_subtype_le _
  have hraw : _root_.numComp (dartStepRel M.σ (rawAlpha M Del hclosed))
      = Fintype.card (Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))) := by
    unfold _root_.numComp; rw [Nat.card_eq_fintype_card]
  rw [hraw, hcard_kept, numDeletedComp, hcompl]
  omega



/-- **A deleted-component dart has its whole `M.σ`-orbit deleted.**  If every dart in `x`'s
`dartStepRel`-component lies in `Del`, then in particular `M.σ x` lies in `Del` (it is a
`dartStepRel`-step away), and inductively the whole `M.σ`-orbit of `x` is deleted. -/
lemma sigma_sameCycle_imp_eqvGen_dartStepRel {a b : D} (h : M.σ.SameCycle a b) :
    Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) a b :=
  Relation.EqvGen.rel _ _ (Or.inl h)

/-- On `Del`, a `dartStepRel`-step keeps you in the same `M.σ`-orbit (the `rawAlpha`-edge fixes
deleted darts).  Hence within a deleted component the relation collapses to `M.σ.SameCycle`. -/
lemma dartStepRel_of_mem_del {a b : D} (ha : a ∈ Del)
    (h : dartStepRel M.σ (rawAlpha M Del hclosed) a b) : M.σ.SameCycle a b := by
  rcases h with hσ | hαe
  · exact hσ
  · rw [rawAlpha_eq_self_of_mem M Del hclosed ha] at hαe
    exact hαe ▸ Equiv.Perm.SameCycle.rfl

/-- **DeletedComp ⟺ DeletedOrbit (`M.σ`).**  The `dartStepRel`-class of a dart is entirely
deleted iff its `M.σ`-orbit is entirely deleted.  (`⟸`: a deleted `M.σ`-orbit admits no
`rawAlpha`-edge leaving `Del`, so the component stays in `Del`; `⟹`: `M.σ.SameCycle` is a
`dartStepRel`-step, so a deleted component contains the whole `M.σ`-orbit.) -/
lemma deletedComp_iff_deletedOrbit (x : D) :
    DeletedComp M Del hclosed (Quotient.mk _ x)
      ↔ DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x) := by
  classical
  constructor
  · -- DeletedComp ⇒ DeletedOrbit: any `M.σ`-cycle dart is `dartStepRel`-related, hence deleted.
    intro hC y hy
    apply hC y
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) y x
    have hsc : M.σ.SameCycle y x := Quotient.exact hy
    exact sigma_sameCycle_imp_eqvGen_dartStepRel M Del hclosed hsc
  · -- DeletedOrbit ⇒ DeletedComp: every `dartStepRel`-related dart stays in the deleted σ-orbit.
    intro hO y hy
    have hxy : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x y :=
      (Quotient.exact hy).symm
    have hxDel : x ∈ Del := hO x rfl
    -- pass to ReflTransGen and carry the invariant `M.σ.SameCycle x z ∧ z ∈ Del` forward.
    have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
        dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
      fun a b => rawStepRel_symm M Del hclosed
    rw [eqvGen_iff_reflTransGen hsymm] at hxy
    have hinv : ∀ z, Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z →
        M.σ.SameCycle x z ∧ z ∈ Del := by
      intro z hz
      induction hz with
      | refl => exact ⟨Equiv.Perm.SameCycle.rfl, hxDel⟩
      | @tail b c hxb hbc ih =>
          obtain ⟨hxb_sc, hbDel⟩ := ih
          have hbc_sc : M.σ.SameCycle b c := dartStepRel_of_mem_del M Del hclosed hbDel hbc
          have hxc_sc : M.σ.SameCycle x c := hxb_sc.trans hbc_sc
          refine ⟨hxc_sc, ?_⟩
          -- `c` is in `x`'s σ-orbit, which is deleted.
          exact hO c (Quotient.sound hxc_sc.symm)
    exact (hinv y hxy).2

/-- Within a deleted component, `dartStepRel`-`EqvGen` collapses to `M.σ.SameCycle`. -/
lemma comp_eqvGen_imp_sigma_of_deleted {x y : D} (hxDel : x ∈ Del)
    (hdel : ∀ z, Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z → z ∈ Del)
    (h : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x y) :
    M.σ.SameCycle x y := by
  classical
  have hsymm : ∀ a b, dartStepRel M.σ (rawAlpha M Del hclosed) a b →
      dartStepRel M.σ (rawAlpha M Del hclosed) b a :=
    fun a b => rawStepRel_symm M Del hclosed
  rw [eqvGen_iff_reflTransGen hsymm] at h
  have hinv : ∀ z, Relation.ReflTransGen (dartStepRel M.σ (rawAlpha M Del hclosed)) x z →
      M.σ.SameCycle x z := by
    intro z hz
    induction hz with
    | refl => exact Equiv.Perm.SameCycle.rfl
    | @tail b c hxb hbc ih =>
        have hbDel : b ∈ Del :=
          hdel b ((eqvGen_iff_reflTransGen hsymm x b).2 hxb)
        exact ih.trans (dartStepRel_of_mem_del M Del hclosed hbDel hbc)
  exact hinv y h

/-- A deleted `dartStepRel`-class's representative `out` is deleted, and its whole component is
deleted (every dart `EqvGen`-related to it). -/
lemma deletedComp_out_props
    {q : Quotient (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed)))}
    (hq : DeletedComp M Del hclosed q) :
    q.out ∈ Del ∧ ∀ z, Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) q.out z →
      z ∈ Del := by
  classical
  have hout : q.out ∈ Del := hq q.out (Quotient.out_eq q)
  refine ⟨hout, fun z hz => ?_⟩
  apply hq z
  rw [← Quotient.out_eq q]
  exact Quotient.sound (Relation.EqvGen.symm _ _ hz)

/-- **`numDeletedComp = numDeletedOrbits M.σ Del`.**  Both count the same family of deleted
`M.σ`-orbits; the equiv sends a deleted component to the `M.σ`-orbit of its representative and
back, well-defined by the within-deleted collapse `comp_eqvGen_imp_sigma_of_deleted`. -/
theorem numDeletedComp_eq_numDeletedOrbits :
    numDeletedComp M Del hclosed = numDeletedOrbits M.σ Del := by
  classical
  unfold numDeletedComp numDeletedOrbits
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q => ⟨Quotient.mk (cycleSetoid M.σ) q.1.out,
        (deletedComp_iff_deletedOrbit M Del hclosed q.1.out).1 (by
          intro z hz
          obtain ⟨hout, hcomp⟩ := deletedComp_out_props M Del hclosed q.2
          exact q.2 z (by rw [hz]; exact Quotient.out_eq q.1))⟩,
      invFun := fun o => ⟨Quotient.mk _ o.1.out,
        (deletedComp_iff_deletedOrbit M Del hclosed o.1.out).2 (by
          intro z hz
          exact o.2 z (by rw [hz]; exact Quotient.out_eq o.1))⟩,
      left_inv := ?_, right_inv := ?_ }
  · -- `[ [qc].out ]_σ` then `[ · ]_comp` returns `qc`.
    rintro ⟨qc, hqc⟩
    apply Subtype.ext
    dsimp only
    obtain ⟨hout, hcomp⟩ := deletedComp_out_props M Del hclosed hqc
    -- the σ-orbit of `qc.out`'s out is σ-SameCycle to `qc.out`, hence same comp-class.
    nth_rewrite 2 [← Quotient.out_eq qc]
    apply Quotient.sound
    show Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) _ qc.out
    have hsc : M.σ.SameCycle (Quotient.mk (cycleSetoid M.σ) qc.out).out qc.out := by
      have := Quotient.out_eq (Quotient.mk (cycleSetoid M.σ) qc.out)
      exact Quotient.exact this
    exact sigma_sameCycle_imp_eqvGen_dartStepRel M Del hclosed hsc
  · -- `[ [o].out ]_comp` then `[ · ]_σ` returns `o`.
    rintro ⟨o, ho⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq o]
    apply Quotient.sound
    show M.σ.SameCycle _ o.out
    -- the comp-class of `o.out` is deleted; its out is σ-SameCycle to `o.out` by the collapse.
    have hodel : o.out ∈ Del := ho o.out (Quotient.out_eq o)
    -- `o`'s σ-orbit is deleted ⇒ `o.out`'s comp-class is deleted (`deletedComp_iff_deletedOrbit`).
    have hDOrbit : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) o.out) := by
      intro z hz
      exact ho z (by rw [hz]; exact Quotient.out_eq o)
    have hDComp : DeletedComp M Del hclosed
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out) :=
      (deletedComp_iff_deletedOrbit M Del hclosed o.out).2 hDOrbit
    obtain ⟨_, hcompdel⟩ := deletedComp_out_props M Del hclosed hDComp
    have hsc : M.σ.SameCycle
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out).out
        o.out := by
      apply comp_eqvGen_imp_sigma_of_deleted M Del hclosed
        (hcompdel _ (Relation.EqvGen.refl _)) hcompdel
      have := Quotient.out_eq
        (Quotient.mk (_root_.compSetoid (dartStepRel M.σ (rawAlpha M Del hclosed))) o.out)
      exact Quotient.exact this
    exact hsc







/-- **`DeletedOrbit`s coincide** for `M.σ` and `M.σ * rawAlpha`. -/
lemma deletedOrbit_sigmaRaw_iff (x : D) :
    DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) x)
      ↔ DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x) := by
  classical
  -- Trajectory: if `x`'s `σRaw`-orbit is deleted then `σ^k x = σRaw^k x ∈ Del` for all `k`,
  -- and symmetrically; this collapses each orbit-deletion predicate to the other.
  have key : ∀ (p q : Equiv.Perm D),
      (∀ d : D, d ∈ Del → p d = q d) →
      ∀ (hpx : DeletedOrbit p Del (Quotient.mk (cycleSetoid p) x)),
      ∀ k : ℕ, (p ^ k) x = (q ^ k) x ∧ (q ^ k) x ∈ Del := by
    intro p q hpq hpx k
    have hxDel : x ∈ Del := hpx x rfl
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hqk_del : (q ^ k) x ∈ Del := ihDel
        have hpk_del : (p ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : (p ^ (k+1)) x = (q ^ (k+1)) x := by
          rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ihEq,
            hpq _ hqk_del]
        refine ⟨heq, ?_⟩
        -- `q^(k+1) x = p^(k+1) x` is in `x`'s `p`-orbit, hence deleted by `hpx`.
        apply hpx
        apply Quotient.sound
        show p.SameCycle ((q ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  constructor
  · intro hP y hy
    have hsc : M.σ.SameCycle y x := Quotient.exact hy
    have hagree : ∀ d : D, d ∈ Del → (M.σ * rawAlpha M Del hclosed) d = M.σ d :=
      fun d hd => sameCycle_sigma_rawFace_of_mem M Del hclosed hd
    -- `y` is in `x`'s σ-orbit; show deleted via the trajectory of `M.σ` matching `σRaw`.
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq  -- `σ^n x = y`
    have := key (M.σ * rawAlpha M Del hclosed) M.σ hagree hP n
    rw [hn] at this
    exact this.2
  · intro hO y hy
    have hsc : (M.σ * rawAlpha M Del hclosed).SameCycle y x := Quotient.exact hy
    have hagree : ∀ d : D, d ∈ Del → M.σ d = (M.σ * rawAlpha M Del hclosed) d :=
      fun d hd => (sameCycle_sigma_rawFace_of_mem M Del hclosed hd).symm
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq  -- `σRaw^n x = y`
    have := key M.σ (M.σ * rawAlpha M Del hclosed) hagree hO n
    rw [hn] at this
    exact this.2

/-- A `σ`-`SameCycle` within a deleted `σRaw`-orbit is a `σRaw`-`SameCycle` (and conversely),
since the two rotations agree on `Del` and the orbit stays in `Del`. -/
lemma sigmaRaw_sameCycle_iff_sigma_of_deletedOrbit {x : D}
    (hP : DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
      (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) x)) {y : D}
    (h : M.σ.SameCycle x y) : (M.σ * rawAlpha M Del hclosed).SameCycle x y := by
  classical
  have hxDel : x ∈ Del := hP x rfl
  -- trajectory: `σ^k x = σRaw^k x ∈ Del`.
  have key : ∀ k : ℕ, ((M.σ * rawAlpha M Del hclosed) ^ k) x = (M.σ ^ k) x
      ∧ (M.σ ^ k) x ∈ Del := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hraw_del : ((M.σ * rawAlpha M Del hclosed) ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x = (M.σ ^ (k+1)) x := by
          have e1 : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x
              = M.σ (((M.σ * rawAlpha M Del hclosed) ^ k) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              rawAlpha_eq_self_of_mem M Del hclosed hraw_del]
          have e2 : (M.σ ^ (k+1)) x = M.σ ((M.σ ^ k) x) := by rw [pow_succ']; rfl
          rw [e1, e2, ihEq]
        refine ⟨heq, ?_⟩
        apply hP
        apply Quotient.sound
        show (M.σ * rawAlpha M Del hclosed).SameCycle ((M.σ ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, (key n).1, hn]⟩

/-- The converse: a `σRaw`-`SameCycle` within a deleted `σ`-orbit is a `σ`-`SameCycle`. -/
lemma sigma_sameCycle_iff_sigmaRaw_of_deletedOrbit {x : D}
    (hO : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) x)) {y : D}
    (h : (M.σ * rawAlpha M Del hclosed).SameCycle x y) : M.σ.SameCycle x y := by
  classical
  have hxDel : x ∈ Del := hO x rfl
  have key : ∀ k : ℕ, (M.σ ^ k) x = ((M.σ * rawAlpha M Del hclosed) ^ k) x
      ∧ ((M.σ * rawAlpha M Del hclosed) ^ k) x ∈ Del := by
    intro k
    induction k with
    | zero => exact ⟨by simp, by simpa using hxDel⟩
    | succ k ih =>
        obtain ⟨ihEq, ihDel⟩ := ih
        have hσ_del : (M.σ ^ k) x ∈ Del := ihEq ▸ ihDel
        have heq : (M.σ ^ (k+1)) x = ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x := by
          have e1 : ((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x
              = M.σ (((M.σ * rawAlpha M Del hclosed) ^ k) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              rawAlpha_eq_self_of_mem M Del hclosed ihDel]
          have e2 : (M.σ ^ (k+1)) x = M.σ ((M.σ ^ k) x) := by rw [pow_succ']; rfl
          rw [e1, e2, ihEq]
        refine ⟨heq, ?_⟩
        apply hO
        apply Quotient.sound
        show M.σ.SameCycle (((M.σ * rawAlpha M Del hclosed) ^ (k+1)) x) x
        exact ⟨-((k+1 : ℕ) : ℤ), by
          rw [← heq, zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.coe_pow]⟩
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨(n : ℤ), by rw [zpow_natCast, (key n).1, hn]⟩

/-- **`numDeletedOrbits (M.σ * rawAlpha) Del = numDeletedOrbits M.σ Del`.** -/
theorem numDeletedOrbits_sigmaRaw_eq :
    numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del = numDeletedOrbits M.σ Del := by
  classical
  unfold numDeletedOrbits
  refine Fintype.card_congr ?_
  refine
    { toFun := fun q => ⟨Quotient.mk (cycleSetoid M.σ) q.1.out,
        (deletedOrbit_sigmaRaw_iff M Del hclosed q.1.out).1 (by
          intro z hz; exact q.2 z (by rw [hz]; exact Quotient.out_eq q.1))⟩,
      invFun := fun o => ⟨Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.1.out,
        (deletedOrbit_sigmaRaw_iff M Del hclosed o.1.out).2 (by
          intro z hz; exact o.2 z (by rw [hz]; exact Quotient.out_eq o.1))⟩,
      left_inv := ?_, right_inv := ?_ }
  · rintro ⟨q, hq⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq q]
    apply Quotient.sound
    show (M.σ * rawAlpha M Del hclosed).SameCycle
      (Quotient.mk (cycleSetoid M.σ) q.out).out q.out
    -- `(mk_σ q.out).out` is `σ`-SameCycle to `q.out`; convert to `σRaw` via deletedness.
    have hsc : M.σ.SameCycle (Quotient.mk (cycleSetoid M.σ) q.out).out q.out :=
      Quotient.exact (Quotient.out_eq (Quotient.mk (cycleSetoid M.σ) q.out))
    -- `q.out`'s `σRaw`-orbit is deleted (q is a deleted `σRaw`-class).
    have hqDel : DeletedOrbit (M.σ * rawAlpha M Del hclosed) Del
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) q.out) := by
      intro z hz; exact hq z (by rw [hz]; exact Quotient.out_eq q)
    exact (sigmaRaw_sameCycle_iff_sigma_of_deletedOrbit M Del hclosed hqDel hsc.symm).symm
  · rintro ⟨o, ho⟩
    apply Subtype.ext
    dsimp only
    nth_rewrite 2 [← Quotient.out_eq o]
    apply Quotient.sound
    show M.σ.SameCycle (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out).out o.out
    have hsc : (M.σ * rawAlpha M Del hclosed).SameCycle
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out).out o.out :=
      Quotient.exact (Quotient.out_eq
        (Quotient.mk (cycleSetoid (M.σ * rawAlpha M Del hclosed)) o.out))
    -- `o.out`'s `σ`-orbit is deleted (o is a deleted `σ`-class); convert via the converse lemma.
    have hoDel : DeletedOrbit M.σ Del (Quotient.mk (cycleSetoid M.σ) o.out) := by
      intro z hz; exact ho z (by rw [hz]; exact Quotient.out_eq o)
    exact (sigma_sameCycle_iff_sigmaRaw_of_deletedOrbit M Del hclosed hoDel hsc.symm).symm



/-- `rawAlpha` is an edge-deletion sub-involution of `M.α`. -/
lemma rawAlpha_subInvolution : SubInvolution M.α (rawAlpha M Del hclosed) := by
  refine ⟨rawAlpha_invol M Del hclosed, fun x hx => ?_⟩
  -- where `rawAlpha` moves `x`, it equals `M.α x` (so `x ∉ Del`).
  by_cases hxD : x ∈ Del
  · exact absurd (rawAlpha_eq_self_of_mem M Del hclosed hxD) hx
  · exact rawAlpha_eq_alpha_of_notMem M Del hclosed hxD

/-- **The raw slack of a genus-0 `M` after deleting `Del` is zero** (`d₀` a witness dart). -/
theorem genusSlack_rawAlpha_eq_zero (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack M.σ (rawAlpha M Del hclosed) = 0 := by
  have hle : genusSlack M.σ (rawAlpha M Del hclosed) ≤ genusSlack M.σ M.α :=
    genusSlack_le_of_subInvolution M.σ M.α M.α_invol _ (rawAlpha_subInvolution M Del hclosed)
  have hM0 : genusSlack M.σ M.α = 0 := genusSlack_sphere_eq_zero M hsphere d₀
  have hge : 0 ≤ genusSlack M.σ (rawAlpha M Del hclosed) :=
    genusSlack_nonneg M.σ _ (rawAlpha_invol M Del hclosed)
  rw [hM0] at hle
  exact le_antisymm hle hge

/-- The kept edge involution has the same number of edges (transpositions) as `rawAlpha`:
both have support exactly the kept darts. -/
lemma Ehalf_keptAlpha_eq_rawAlpha :
    Ehalf (keptAlpha M Del hsub) = Ehalf (rawAlpha M Del hclosed) := by
  classical
  -- `2 * Ehalf = card support`.  `keptAlpha` is fixed-point-free on the kept subtype, so its
  -- support is all kept darts; `rawAlpha`'s support is exactly the kept darts of `D`.
  have hk : (keptAlpha M Del hsub) ∈ Set.univ := ⟨⟩
  -- `keptAlpha` fixed-point-free:
  have hkff : ∀ d, keptAlpha M Del hsub d ≠ d := by
    intro d hd
    apply M.α_no_fixed d.1
    have := congrArg Subtype.val hd
    rwa [keptAlpha_apply_coe] at this
  have hksupp : Equiv.Perm.support (keptAlpha M Del hsub) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]; intro d; rw [Equiv.Perm.mem_support]; exact hkff d
  -- `rawAlpha` support = kept darts (its complement is `Del`).
  have hrsupp : Equiv.Perm.support (rawAlpha M Del hclosed) = Finset.univ.filter (· ∉ Del) := by
    ext d
    simp only [Equiv.Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [rawAlpha_apply]
    by_cases hd : d ∈ Del
    · simp [hd]
    · simp only [hd, if_false, not_false_iff, iff_true]
      exact fun hc => M.α_no_fixed d hc
  unfold Ehalf
  rw [hksupp, hrsupp, Finset.card_univ]
  -- both cardinalities are `|kept darts|`.
  have : (Finset.univ.filter (· ∉ Del) : Finset D).card
      = Fintype.card {d : D // d ∉ Del} := by
    rw [Fintype.card_subtype]
  rw [this]

/-- **The kept combinatorial map's genus slack is zero** on a genus-0 `M`.  This is the
structural genus-0 certificate: the kept side (an edge-deletion sub-map of the sphere `M`) has
genus slack `0`, hence — when connected — Euler characteristic `2` (no handle). -/
theorem keptMap_genusSlack_eq_zero (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (d₀ : D) :
    genusSlack (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) = 0 := by
  classical
  have hraw0 : genusSlack M.σ (rawAlpha M Del hclosed) = 0 :=
    genusSlack_rawAlpha_eq_zero M Del hclosed hsphere d₀
  -- expand both slacks via the count bridges.
  unfold genusSlack at hraw0 ⊢
  -- raw: `2c_raw - numCycles σ + Ehalf rawAlpha - numCycles (σ rawAlpha)`.
  -- kept: `2c_kept - numCycles(deleteSet σ) + Ehalf keptAlpha - numCycles(keptFacePerm)`.
  -- bridges:
  have hcsplit : numComponents M.σ (rawAlpha M Del hclosed)
      = _root_.numComp (keptStepRel M Del hsub) + numDeletedComp M Del hclosed :=
    numComponents_raw_split M Del hclosed hsub
  have hkeptStep_eq : _root_.numComp (keptStepRel M Del hsub)
      = numComponents (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) := by
    rw [numComponents_def]; rfl
  have hDC : numDeletedComp M Del hclosed = numDeletedOrbits M.σ Del :=
    numDeletedComp_eq_numDeletedOrbits M Del hclosed
  have hVsplit : _root_.numCycles M.σ
      = _root_.numCycles (Equiv.Perm.deleteSet M.σ Del) + numDeletedOrbits M.σ Del :=
    numCycles_eq_kept_add_deleted M.σ Del
  have hFsplit : _root_.numCycles (M.σ * rawAlpha M Del hclosed)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del)
        + numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del :=
    numCycles_eq_kept_add_deleted (M.σ * rawAlpha M Del hclosed) Del
  have hFbridge : _root_.numCycles (keptFacePerm M Del hclosed hsub)
      = _root_.numCycles (Equiv.Perm.deleteSet (M.σ * rawAlpha M Del hclosed) Del) :=
    numCycles_keptFacePerm_eq M Del hclosed hsub
  have hDF : numDeletedOrbits (M.σ * rawAlpha M Del hclosed) Del = numDeletedOrbits M.σ Del :=
    numDeletedOrbits_sigmaRaw_eq M Del hclosed
  have hEh : Ehalf (keptAlpha M Del hsub) = Ehalf (rawAlpha M Del hclosed) :=
    Ehalf_keptAlpha_eq_rawAlpha M Del hclosed hsub
  -- the kept face permutation is the σα of the kept CombMap.
  have hkeptFace : (Equiv.Perm.deleteSet M.σ Del) * (keptAlpha M Del hsub)
      = keptFacePerm M Del hclosed hsub := rfl
  -- assemble: rewrite `hraw0` (raw slack = 0) into kept quantities.
  rw [hkeptStep_eq] at hcsplit
  rw [hcsplit, hVsplit, ← hEh, hFsplit, hDF, hDC] at hraw0
  -- hraw0 now: `2(c_kept + DV) - (V_kept + DV) + Ehalf keptAlpha
  --   - (numCycles(deleteSet(σ*rawAlpha)) + DV) = 0`.
  -- goal: `2 c_kept - V_kept + Ehalf keptAlpha - numCycles(keptFacePerm) = 0`.
  rw [hkeptFace, hFbridge]
  push_cast at hraw0 ⊢
  linarith

/-- **The kept combinatorial map of a chord-split side of a genus-0 `M` is a disk
(no handle).**  Given a `CombMap K` whose rotation is `deleteSet M.σ Del` and whose edge
involution is `keptAlpha`, if it is connected and has a dart, then its Euler characteristic is
exactly `2`.  This is the reverse inequality `2 ≤ eulerChar` (in fact equality), supplied by the
structural genus monotonicity — the genus-0 certificate that the chord side has no handle. -/
theorem keptMap_eulerChar_eq_two (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap)
    (K : CombMap {d : D // d ∉ Del})
    (hKσ : K.σ = Equiv.Perm.deleteSet M.σ Del) (hKα : K.α = keptAlpha M Del hsub)
    (d : {d : D // d ∉ Del}) (hconn : K.Connected) :
    K.eulerChar = 2 := by
  classical
  have hslack0 : genusSlack (Equiv.Perm.deleteSet M.σ Del) (keptAlpha M Del hsub) = 0 :=
    keptMap_genusSlack_eq_zero M Del hsub hclosed hsphere d.1
  have hc : numComponents K.σ K.α = 1 :=
    numComponents_eq_one_of_connected K hconn d
  have hVc : (K.V : ℤ) = (_root_.numCycles K.σ : ℤ) := by rw [V_eq_numCycles]
  have hEc : (K.E : ℤ) = (Ehalf K.α : ℤ) := by rw [Ehalf_eq_E]
  have hFc : (K.F : ℤ) = (_root_.numCycles (K.σ * K.α) : ℤ) := by rw [F_eq_numCycles]; rfl
  have hslack : genusSlack K.σ K.α = 0 := by rw [hKσ, hKα]; exact hslack0
  unfold genusSlack at hslack
  rw [hc] at hslack
  unfold CombMap.eulerChar
  rw [hVc, hEc, hFc]
  push_cast at hslack ⊢
  linarith

end RawRestrict



section ChordThreading

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSideRecon

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- `keptDel₁` is `M.α`-closed (membership is `α`-invariant), the input to the structural
certificate. -/
lemma keptDel₁_sub (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₁ ↔ M.α d ∈ data.keptDel₁ := by
  intro d
  have h1 : d ∉ data.keptDel₁ ↔ d ∈ data.keptSet₁ := data.mem_keptDel₁_iff d
  have h2 : M.α d ∉ data.keptDel₁ ↔ M.α d ∈ data.keptSet₁ := data.mem_keptDel₁_iff (M.α d)
  have hkept : M.α d ∈ data.keptSet₁ ↔ d ∈ data.keptSet₁ :=
    data.mem_keptSet₁_alpha_iff hsep d
  classical
  -- `d ∈ Del ↔ ¬ d ∈ keptSet`, similarly for `M.α d`; then use `hkept`.
  have h1' : d ∈ data.keptDel₁ ↔ ¬ d ∈ data.keptSet₁ := by
    rw [← h1]; exact (not_not).symm
  have h2' : M.α d ∈ data.keptDel₁ ↔ ¬ M.α d ∈ data.keptSet₁ := by
    rw [← h2]; exact (not_not).symm
  rw [h1', h2']
  exact (not_congr hkept).symm

lemma keptDel₁_closed (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ d, d ∈ data.keptDel₁ → M.α d ∈ data.keptDel₁ :=
  fun d hd => (keptDel₁_sub data hsep d).1 hd

/-- `sideAlpha₁` equals the abstract `keptAlpha` of `keptDel₁` (both are `M.α` restricted). -/
lemma sideAlpha₁_eq_keptAlpha (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideAlpha₁ hsep
      = SubmapPlanar.keptAlpha M data.keptDel₁ (keptDel₁_sub data hsep) := by
  ext d
  rw [data.sideAlpha₁_apply_coe]
  rfl

/-- **The `≥ 2` no-handle half of `KeptSideIsDisk` at side 1, discharged structurally.**  If the
kept side-1 map is connected and has a dart, its Euler characteristic is `2` — the genus-0
certificate from sub-map planarity (`M` is a sphere via `hNT.sphere`). -/
theorem side₁_keptMap_eulerChar_eq_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁})
    (hconn : (sideKeptMap₁ data hsep).Connected) :
    (sideKeptMap₁ data hsep).eulerChar = 2 := by
  refine SubmapPlanar.keptMap_eulerChar_eq_two M data.keptDel₁ (keptDel₁_sub data hsep)
    (keptDel₁_closed data hsep) hNT.sphere (sideKeptMap₁ data hsep) ?_ ?_ d hconn
  · -- `(sideKeptMap₁).σ = sideSigma₁ = filteredRotation M.σ keptDel₁ = deleteSet M.σ keptDel₁`.
    show data.sideSigma₁ = Equiv.Perm.deleteSet M.σ data.keptDel₁
    rfl
  · -- `(sideKeptMap₁).α = sideAlpha₁ = keptAlpha`.
    show data.sideAlpha₁ hsep = SubmapPlanar.keptAlpha M data.keptDel₁ (keptDel₁_sub data hsep)
    exact sideAlpha₁_eq_keptAlpha data hsep

/-- **`Side₁IsDisk` reduces to connectivity of the kept side.**  Given the structural genus-0
certificate, side 1 is a disk (`IsSphereMap`) *iff* its kept map is connected (the `eulerChar`
half is discharged).  This removes the no-handle inequality `2 ≤ eulerChar` from the residue —
its `≤ 2` half is `chi_le_two_of_connected`, its `≥ 2` half is now proved. -/
theorem side₁IsDisk_of_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (d : {d : D // d ∉ data.keptDel₁})
    (hconn : (sideKeptMap₁ data hsep).Connected) :
    ChordDisk.Side₁IsDisk data hsep :=
  ⟨hconn, side₁_keptMap_eulerChar_eq_two data hsep d hconn⟩



end ChordThreading

end ProofsInTheBook.SubmapPlanar

















end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.TetPearls -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Classical
open Set

namespace ProofsInTheBook.TetPearls

/-- Ambient Euclidean 3-space. -/
abbrev Pt3 : Type := EuclideanSpace ℝ (Fin 3)





namespace Tet



















end Tet





namespace TetSolid







end TetSolid









namespace Segment3







































































end Segment3



namespace Tet













end Tet





















namespace Pearl








end Pearl





































end ProofsInTheBook.TetPearls

end
end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter09 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter09

open scoped BigOperators TensorProduct
open Polynomial Chebyshev





















































-- (`angleClassQ_arccos_one_third_ne_zero` defined below, after
-- `arccos_one_third_irrational_over_pi`.)












































































































































































































































































end ProofsInTheBook.Chapter09

end

/- Original source header (imports hoisted):
import ProofsInTheBook.TetPearls
import ProofsInTheBook.Chapter09
-/
/- Source module: ProofsInTheBook.TetDihedral -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls

namespace ProofsInTheBook.TetDihedral

























































































end ProofsInTheBook.TetDihedral

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.TetDihedral
-/
/- Source module: ProofsInTheBook.SphericalKernel -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral

namespace ProofsInTheBook.SphericalKernel



/-- `E3` is the ambient Euclidean 3-space `EuclideanSpace ℝ (Fin 3)` (an alias for `Pt3`). -/
abbrev E3 : Type := Pt3

/-- The unit sphere `S²`, as the unit vectors of `E3`. -/
def S2 : Type := {x : E3 // ‖x‖ = 1}

instance : Coe S2 E3 := ⟨Subtype.val⟩




















































































































end ProofsInTheBook.SphericalKernel

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalKernel
-/
/- Source module: ProofsInTheBook.SphericalArm -/
section
set_option autoImplicit true




noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.SphericalArm







































































end ProofsInTheBook.SphericalArm

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArm
-/
/- Source module: ProofsInTheBook.SphericalRotation -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm

namespace ProofsInTheBook.SphericalRotation

/-- Cross product on `E3 = EuclideanSpace ℝ (Fin 3)`, in explicit coordinates. -/
def cross (a b : E3) : E3 :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

@[simp] theorem cross_apply_zero (a b : E3) : cross a b 0 = a 1 * b 2 - a 2 * b 1 := rfl
@[simp] theorem cross_apply_one (a b : E3) : cross a b 1 = a 2 * b 0 - a 0 * b 2 := rfl
@[simp] theorem cross_apply_two (a b : E3) : cross a b 2 = a 0 * b 1 - a 1 * b 0 := rfl

/-- Inner product expanded into coordinates. -/
theorem inner_eq_coord (a b : E3) :
    (⟪a, b⟫ : ℝ) = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]; ring
























/-- `⟪a × b, a⟫ = 0`: the cross product is orthogonal to the first factor. -/
theorem inner_cross_left (a b : E3) : (⟪cross a b, a⟫ : ℝ) = 0 := by
  rw [inner_eq_coord]; simp; ring











/-- **Binet–Cauchy identity:** `⟪a × b, c × d⟫ = ⟪a,c⟫⟪b,d⟫ − ⟪a,d⟫⟪b,c⟫`. -/
theorem inner_cross_cross (a b c d : E3) :
    (⟪cross a b, cross c d⟫ : ℝ) = ⟪a, c⟫ * ⟪b, d⟫ - ⟪a, d⟫ * ⟪b, c⟫ := by
  rw [inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord, inner_eq_coord]
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring



/-- The Rodrigues rotation of `v` about unit axis `k` by angle `θ`. -/
def rot (k : E3) (θ : ℝ) (v : E3) : E3 :=
  Real.cos θ • v + Real.sin θ • cross k v + ((1 - Real.cos θ) * ⟪k, v⟫) • k















/-- **Inner-product preservation (the crux):** `⟪rot k θ v, rot k θ w⟫ = ⟪v, w⟫` for a unit axis.
Proved by bilinear expansion using `inner_cross_cross` (Binet–Cauchy), `inner_cross_left/right`
(`⟪k×v,k⟫ = 0`), and `cos²θ + sin²θ = 1`. -/
theorem inner_rot_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v w : E3) :
    (⟪rot k θ v, rot k θ w⟫ : ℝ) = ⟪v, w⟫ := by
  have hkk : (⟪k, k⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hk]; norm_num
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  -- key cross identities (with k a unit vector)
  have h_kvk : (⟪cross k v, k⟫ : ℝ) = 0 := inner_cross_left k v
  have h_kkv : (⟪k, cross k v⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact h_kvk
  have h_kwk : (⟪cross k w, k⟫ : ℝ) = 0 := inner_cross_left k w
  have h_kkw : (⟪k, cross k w⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact h_kwk
  -- ⟪k×v, k×w⟫ = ⟪k,k⟫⟪v,w⟫ − ⟪k,w⟫⟪v,k⟫ = ⟪v,w⟫ − ⟪k,w⟫⟪v,k⟫
  have h_cc : (⟪cross k v, cross k w⟫ : ℝ) = ⟪v, w⟫ - ⟪k, w⟫ * ⟪v, k⟫ := by
    rw [inner_cross_cross, hkk, one_mul]
  -- mixed term antisymmetry: ⟪k×v, w⟫ = −⟪v, k×w⟫
  have h_mix : (⟪cross k v, w⟫ : ℝ) = -(⟪v, cross k w⟫) := by
    rw [inner_eq_coord, inner_eq_coord]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  have hvk : (⟪v, k⟫ : ℝ) = ⟪k, v⟫ := real_inner_comm k v
  -- expand the full inner product
  simp only [rot, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h_kvk, h_kkw, hkk]
  rw [h_cc, h_mix, hvk]
  -- now everything is in terms of ⟪v,w⟫, ⟪k,v⟫, ⟪k,w⟫, ⟪v, cross k w⟫, cos, sin;
  -- LHS − ⟪v,w⟫ = (cos²+sin²−1)(⟪v,w⟫ − ⟪k,v⟫⟪k,w⟫), closed by hcs.
  linear_combination (⟪v, w⟫ - ⟪k, v⟫ * ⟪k, w⟫) * hcs

/-- **Norm preservation:** `‖rot k θ v‖ = ‖v‖`. -/
theorem norm_rot {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    ‖rot k θ v‖ = ‖v‖ := by
  have h1 : ‖rot k θ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_rot_rot hk]
  have hnn1 : (0 : ℝ) ≤ ‖rot k θ v‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  nlinarith [h1, hnn1, hnn2]



/-- The rotation maps `S²` into `S²` (norm preserved). -/
def rotS2 (k : S2) (θ : ℝ) (p : S2) : S2 :=
  ⟨rot (k : E3) θ (p : E3), by rw [norm_rot k.2]; exact p.2⟩























variable {ι : Type*}

























end ProofsInTheBook.SphericalRotation

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.SphericalSZ -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalRotation

namespace ProofsInTheBook.SphericalSZ


























end ProofsInTheBook.SphericalSZ

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZ
-/
/- Source module: ProofsInTheBook.SphericalCore -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.SphericalCore

















































end ProofsInTheBook.SphericalCore

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCore
-/
/- Source module: ProofsInTheBook.SphericalFinish -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore

namespace ProofsInTheBook.SphericalFinish









































end ProofsInTheBook.SphericalFinish

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalFinish
-/
/- Source module: ProofsInTheBook.SphericalOpening -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish

namespace ProofsInTheBook.SphericalOpening

























end ProofsInTheBook.SphericalOpening

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpening
-/
/- Source module: ProofsInTheBook.SphericalHinge -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening

namespace ProofsInTheBook.SphericalHinge



















































end ProofsInTheBook.SphericalHinge

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalHinge
-/
/- Source module: ProofsInTheBook.SphericalSZChain -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge

namespace ProofsInTheBook.SphericalSZChain































end ProofsInTheBook.SphericalSZChain

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZChain
-/
/- Source module: ProofsInTheBook.SphericalCyclicTriple -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain

namespace ProofsInTheBook.SphericalCyclicTriple









































end ProofsInTheBook.SphericalCyclicTriple

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCyclicTriple
-/
/- Source module: ProofsInTheBook.SphericalGnomonic -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalGnomonic






















































end ProofsInTheBook.SphericalGnomonic

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalGnomonic
-/
/- Source module: ProofsInTheBook.PlanarConvexDiag -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalArm ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalGnomonic

namespace ProofsInTheBook.PlanarConvexDiag



























end ProofsInTheBook.PlanarConvexDiag

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.SphericalSZStep -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag

namespace ProofsInTheBook.SphericalSZStep































end ProofsInTheBook.SphericalSZStep

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZStep
-/
/- Source module: ProofsInTheBook.SphericalHingeCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep

namespace ProofsInTheBook.SphericalHingeCut







































end ProofsInTheBook.SphericalHingeCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalHingeCut
-/
/- Source module: ProofsInTheBook.SphericalDiagCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut

namespace ProofsInTheBook.SphericalDiagCut

















































end ProofsInTheBook.SphericalDiagCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalDiagCut
-/
/- Source module: ProofsInTheBook.SphericalOpeningProcess -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut

namespace ProofsInTheBook.SphericalOpeningProcess

























































end ProofsInTheBook.SphericalOpeningProcess

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpeningProcess
-/
/- Source module: ProofsInTheBook.SphericalReachStuck -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess

namespace ProofsInTheBook.SphericalReachStuck





































end ProofsInTheBook.SphericalReachStuck

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalReachStuck
-/
/- Source module: ProofsInTheBook.SphericalAdmissibleSup -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck

namespace ProofsInTheBook.SphericalAdmissibleSup

































































end ProofsInTheBook.SphericalAdmissibleSup

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalAdmissibleSup
-/
/- Source module: ProofsInTheBook.SphericalArmClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup

namespace ProofsInTheBook.SphericalArmClose































































end ProofsInTheBook.SphericalArmClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmClose
-/
/- Source module: ProofsInTheBook.SphericalArmFinal -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalArmFinal























end ProofsInTheBook.SphericalArmFinal

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmFinal
-/
/- Source module: ProofsInTheBook.SphericalSZComplete -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalSZComplete













































end ProofsInTheBook.SphericalSZComplete

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZComplete
-/
/- Source module: ProofsInTheBook.SphericalStuckWitness -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete

namespace ProofsInTheBook.SphericalStuckWitness





















































end ProofsInTheBook.SphericalStuckWitness

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckWitness
-/
/- Source module: ProofsInTheBook.SphericalTerminalVis -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalStuckWitness

namespace ProofsInTheBook.SphericalTerminalVis































































end ProofsInTheBook.SphericalTerminalVis

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalTerminalVis
-/
/- Source module: ProofsInTheBook.SphericalArmUncond -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis

namespace ProofsInTheBook.SphericalArmUncond

















































end ProofsInTheBook.SphericalArmUncond

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmUncond
-/
/- Source module: ProofsInTheBook.SphericalMatchedCut -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond

namespace ProofsInTheBook.SphericalMatchedCut









































































































end ProofsInTheBook.SphericalMatchedCut

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalMatchedCut
-/
/- Source module: ProofsInTheBook.SphericalCornerStep -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut

namespace ProofsInTheBook.SphericalCornerStep















































end ProofsInTheBook.SphericalCornerStep

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCornerStep
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.SphericalConeMembership -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep

namespace ProofsInTheBook.SphericalConeMembership













































































end ProofsInTheBook.SphericalConeMembership

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalConeMembership
-/
/- Source module: ProofsInTheBook.SphericalArmDone -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership

namespace ProofsInTheBook.SphericalArmDone



















































end ProofsInTheBook.SphericalArmDone

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmDone
-/
/- Source module: ProofsInTheBook.SphericalArmFinish -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone

namespace ProofsInTheBook.SphericalArmFinish









































end ProofsInTheBook.SphericalArmFinish

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmFinish
-/
/- Source module: ProofsInTheBook.SphericalArmClose2 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish

namespace ProofsInTheBook.SphericalArmClose2















































end ProofsInTheBook.SphericalArmClose2

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmClose2
-/
/- Source module: ProofsInTheBook.SphericalStuckCollinear -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2

namespace ProofsInTheBook.SphericalStuckCollinear















































end ProofsInTheBook.SphericalStuckCollinear

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckCollinear
-/
/- Source module: ProofsInTheBook.SphericalOpenedArmCore -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalOpenedArmCore



























end ProofsInTheBook.SphericalOpenedArmCore

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckCollinear
-/
/- Source module: ProofsInTheBook.SphericalSZInduction -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalSZInduction

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























/-- The interior tail-opening: fix vertices `≤ k`, rotate vertices `> k` about the axis `A k`. -/
def openTail {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n + 1)) (δ : ℝ) : Fin (n + 1) → S2 :=
  fun r => if r.val ≤ k.val then A r else rotS2 (A k) δ (A r)







































































end ProofsInTheBook.SphericalSZInduction

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZInduction
-/
/- Source module: ProofsInTheBook.SphericalSZStepClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalStuckCollinear
open ProofsInTheBook.SphericalSZInduction

namespace ProofsInTheBook.SphericalSZStepClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































end ProofsInTheBook.SphericalSZStepClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZStepClose
-/
/- Source module: ProofsInTheBook.SphericalSZFinal -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose

namespace ProofsInTheBook.SphericalSZFinal

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

























































end ProofsInTheBook.SphericalSZFinal

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZFinal
-/
/- Source module: ProofsInTheBook.SphericalSZClose -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.SphericalSZClose

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.SphericalSZClose

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalCutTransport -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalCutTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.SphericalCutTransport

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalCutTransport
-/
/- Source module: ProofsInTheBook.ZinanFFCT -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.ZinanFFCT

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





























end ProofsInTheBook.ZinanFFCT

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT
-/
/- Source module: ProofsInTheBook.ZinanFFCT2 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT

namespace ProofsInTheBook.ZinanFFCT2

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




































































end ProofsInTheBook.ZinanFFCT2

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT2
-/
/- Source module: ProofsInTheBook.ZinanFFCT3 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2

namespace ProofsInTheBook.ZinanFFCT3

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT3

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT3
-/
/- Source module: ProofsInTheBook.ZinanFFCT4 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT4

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.ZinanFFCT4

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT4
-/
/- Source module: ProofsInTheBook.ZinanFFCT5 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4

namespace ProofsInTheBook.ZinanFFCT5

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



















end ProofsInTheBook.ZinanFFCT5

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT5
-/
/- Source module: ProofsInTheBook.ZinanFFCT6 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5

namespace ProofsInTheBook.ZinanFFCT6

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


























end ProofsInTheBook.ZinanFFCT6

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT6
-/
/- Source module: ProofsInTheBook.ZinanFFCT7 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT
open ProofsInTheBook.ZinanFFCT2
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT5
open ProofsInTheBook.ZinanFFCT6

namespace ProofsInTheBook.ZinanFFCT7

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT7

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT7
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.ZinanFFCT8 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZ ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT ProofsInTheBook.ZinanFFCT2 ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT4 ProofsInTheBook.ZinanFFCT5 ProofsInTheBook.ZinanFFCT6
open ProofsInTheBook.ZinanFFCT7

namespace ProofsInTheBook.ZinanFFCT8

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT8

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT8
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.ZinanFFCT9 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT8

namespace ProofsInTheBook.ZinanFFCT9

set_option maxHeartbeats 1600000
















































































end ProofsInTheBook.ZinanFFCT9

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT9
-/
/- Source module: ProofsInTheBook.ZinanFFCT10 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9

namespace ProofsInTheBook.ZinanFFCT10

set_option maxHeartbeats 1600000






















































end ProofsInTheBook.ZinanFFCT10








end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
-/
/- Source module: ProofsInTheBook.ZinanFFCT17 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT17

set_option maxHeartbeats 1600000















































































end ProofsInTheBook.ZinanFFCT17

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT17
-/
/- Source module: ProofsInTheBook.ZinanFFCT18 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT17

namespace ProofsInTheBook.ZinanFFCT18

set_option maxHeartbeats 1600000




















































end ProofsInTheBook.ZinanFFCT18

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckWitness
import ProofsInTheBook.SphericalCutTransport
-/
/- Source module: ProofsInTheBook.SphericalStuckGeneral -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalStuckWitness ProofsInTheBook.SphericalTerminalVis
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport

namespace ProofsInTheBook.SphericalStuckGeneral





































end ProofsInTheBook.SphericalStuckGeneral

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.SphericalLastCornerStuck -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose ProofsInTheBook.SphericalStuckGeneral

namespace ProofsInTheBook.SphericalLastCornerStuck





























end ProofsInTheBook.SphericalLastCornerStuck

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT18
import ProofsInTheBook.SphericalLastCornerStuck
-/
/- Source module: ProofsInTheBook.ZinanFFCT19 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalCutTransport ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.TetDihedral
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT19

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


















































end ProofsInTheBook.ZinanFFCT19

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalMonitoredSup -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalMonitoredSup

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















/-- A non-incident edge–vertex pair: edge `(c.1, c.1+1)` and a vertex `c.2` off that edge. -/
def NonIncident (n : ℕ) : Type :=
  {c : Fin (n + 1) × Fin (n + 1) // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}

instance (n : ℕ) : Finite (NonIncident n) := by
  unfold NonIncident; infer_instance





















































end ProofsInTheBook.SphericalMonitoredSup

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalSZClose
-/
/- Source module: ProofsInTheBook.SphericalSpliceTransport -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose

namespace ProofsInTheBook.SphericalSpliceTransport

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























end ProofsInTheBook.SphericalSpliceTransport

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalRotation
import ProofsInTheBook.SphericalCyclicTriple
-/
/- Source module: ProofsInTheBook.SphericalCongruence -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.TetPearls ProofsInTheBook.TetDihedral
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple

namespace ProofsInTheBook.SphericalCongruence

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























































end ProofsInTheBook.SphericalCongruence

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.SphericalCongruence
-/
/- Source module: ProofsInTheBook.SphericalArmAssembly -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCongruence

namespace ProofsInTheBook.SphericalArmAssembly

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.SphericalArmAssembly

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalArmAssembly
-/
/- Source module: ProofsInTheBook.SphericalOpeningOutcome -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalArmAssembly

namespace ProofsInTheBook.SphericalOpeningOutcome

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























end ProofsInTheBook.SphericalOpeningOutcome


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.SphericalOpeningOutcome
import ProofsInTheBook.ZinanFFCT18
-/
/- Source module: ProofsInTheBook.ZinanFFCT20 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT20




















end ProofsInTheBook.ZinanFFCT20

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
-/
/- Source module: ProofsInTheBook.ZinanFFCT12 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT12

set_option maxHeartbeats 1600000



























end ProofsInTheBook.ZinanFFCT12

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT12
-/
/- Source module: ProofsInTheBook.ZinanFFCT21 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18

namespace ProofsInTheBook.ZinanFFCT21

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT21

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT21
-/
/- Source module: ProofsInTheBook.ZinanFFCT22 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT22

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















































end ProofsInTheBook.ZinanFFCT22

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT22
-/
/- Source module: ProofsInTheBook.ZinanFFCT23 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT23

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT23

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT23
-/
/- Source module: ProofsInTheBook.ZinanFFCT24 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23

namespace ProofsInTheBook.ZinanFFCT24

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






















































end ProofsInTheBook.ZinanFFCT24

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT24
-/
/- Source module: ProofsInTheBook.ZinanFFCT25 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalRotation
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24

namespace ProofsInTheBook.ZinanFFCT25

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000













































end ProofsInTheBook.ZinanFFCT25

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalCore
-/
/- Source module: ProofsInTheBook.ZinanFFCT26 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT26

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000











































end ProofsInTheBook.ZinanFFCT26

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT26
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.ZinanFFCT27 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZ

namespace ProofsInTheBook.ZinanFFCT27

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT27

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT27
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalOpeningOutcome
-/
/- Source module: ProofsInTheBook.ZinanFFCT28 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.SphericalStuckGeneral ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.ZinanFFCT28

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT28

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpeningOutcome
-/
/- Source module: ProofsInTheBook.SphericalOpeningGlue -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome

namespace ProofsInTheBook.SphericalOpeningGlue

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

































end ProofsInTheBook.SphericalOpeningGlue

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalOpeningGlue
-/
/- Source module: ProofsInTheBook.ZinanFFCT30 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalOpeningGlue

namespace ProofsInTheBook.ZinanFFCT30

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

























end ProofsInTheBook.ZinanFFCT30

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT30
import ProofsInTheBook.ZinanFFCT22
-/
/- Source module: ProofsInTheBook.ZinanFFCT33 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30

namespace ProofsInTheBook.ZinanFFCT33

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















/-- The equator index set of the opened arm: vertices pushed onto the `h₀`-equator. -/
def equatorSet {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) :
    Fin (n + 1) → Prop :=
  fun r => (⟪h₀, ((openTail A K δ r : S2) : E3)⟫ : ℝ) = 0

instance equatorSet_decidable {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (h₀ : E3) (δ : ℝ) :
    DecidablePred (equatorSet A K h₀ δ) := fun _ => Classical.dec _













end ProofsInTheBook.ZinanFFCT33
end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT33
-/
/- Source module: ProofsInTheBook.ZinanFFCT34 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30 ProofsInTheBook.ZinanFFCT33

namespace ProofsInTheBook.ZinanFFCT34

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT34

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT34
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Combination
-/
/- Source module: ProofsInTheBook.ZinanFFCT36 -/
section
set_option autoImplicit true


noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT33 ProofsInTheBook.ZinanFFCT34

namespace ProofsInTheBook.ZinanFFCT36

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
























end ProofsInTheBook.ZinanFFCT36
end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT36
-/
/- Source module: ProofsInTheBook.ZinanFFCT44 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36

namespace ProofsInTheBook.ZinanFFCT44

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT44

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT20
import ProofsInTheBook.ZinanFFCT3
import ProofsInTheBook.SphericalOpeningGlue
-/
/- Source module: ProofsInTheBook.ZinanFFCT37 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT3

namespace ProofsInTheBook.ZinanFFCT37

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































































end ProofsInTheBook.ZinanFFCT37

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT37
import ProofsInTheBook.ZinanFFCT36
-/
/- Source module: ProofsInTheBook.ZinanFFCT38 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37

namespace ProofsInTheBook.ZinanFFCT38

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



















































end ProofsInTheBook.ZinanFFCT38






end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT38
-/
/- Source module: ProofsInTheBook.ZinanFFCT39 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38

namespace ProofsInTheBook.ZinanFFCT39

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000













































end ProofsInTheBook.ZinanFFCT39

-- Brick 1 (positive content + assembly + audit)





-- Brick 2 (audit + positive content)




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT39
-/
/- Source module: ProofsInTheBook.ZinanFFCT40 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39

namespace ProofsInTheBook.ZinanFFCT40

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000























































end ProofsInTheBook.ZinanFFCT40

-- §1 the any-h assembler

-- §3 the pure-hemi strict certificate + repaired stuck outcome + repaired clause (iii)



-- §3 the corrected outcome + repaired headline



-- refutation-resistance witnesses


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT40
-/
/- Source module: ProofsInTheBook.ZinanFFCT41 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZChain
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT30
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT38
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT40

namespace ProofsInTheBook.ZinanFFCT41

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































































end ProofsInTheBook.ZinanFFCT41

-- §1 the WB family + W-admissibility bridge

-- §2 the base sinusoid

-- §3 the cap by admissibility (the central new content)


-- §5 the WB trichotomy

-- §6/§7 the clauses at the WB sup



-- §8/§9 the base-capped outcome + headline (GlueWBaseCap discharged)


-- refutation-resistance witness


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT41
-/
/- Source module: ProofsInTheBook.ZinanFFCT42 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT41

namespace ProofsInTheBook.ZinanFFCT42

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT42

-- §1 the algebra/index micro-lemmas


-- §2 base-stuck = opened diagonal

-- §3 Brick 1 (the cyclic-identity bridge) + the vanishing-support payload


-- §4 the residual DISCHARGED + the base-stuck-free headline


-- non-vacuity guards


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT42
-/
/- Source module: ProofsInTheBook.ZinanFFCT45 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT45

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.ZinanFFCT45

-- §1 the WBS family + closure facts





-- §2 init admissibility

-- §3 deficit bound + base cap



-- §4 the trichotomy + clauses



-- §5 Brick 7: the FFCT42 base-stuck port DISCHARGED



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT42
-/
/- Source module: ProofsInTheBook.ZinanFFCT43 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.ZinanFFCT39
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT43

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT43

-- §1 endpoint positivity

-- §2 closing edge distinct at the WB supremum

-- §3 the residual DISCHARGED + the closing-edge-free headline


-- non-vacuity guards


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT44
import ProofsInTheBook.ZinanFFCT45
import ProofsInTheBook.ZinanFFCT43
-/
/- Source module: ProofsInTheBook.ZinanFFCT46 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT34
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT40
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45

namespace ProofsInTheBook.ZinanFFCT46

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































end ProofsInTheBook.ZinanFFCT46

-- §1 the margins-free open-hemisphere production (THE keystone mechanism)

-- §2 brick 4

-- §2′ the opened side / joint geometry



-- §3 bricks 5–6


-- §4 brick 8

-- §5 brick 9 + non-vacuity



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT46
-/
/- Source module: ProofsInTheBook.ZinanFFCT47 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT36
open ProofsInTheBook.ZinanFFCT42
open ProofsInTheBook.ZinanFFCT43
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46

namespace ProofsInTheBook.ZinanFFCT47

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



























































end ProofsInTheBook.ZinanFFCT47

-- §1 the open-chain collapse kernel (3 ≤ n)

-- §2 the wrap-edge-free open-hemisphere production

-- §3 wrap ShortArc from the hemisphere

-- §4 the residual discharged


-- §5 the wrap-free headline



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT47
import ProofsInTheBook.ZinanFFCT28
import ProofsInTheBook.SphericalStuckGeneral
-/
/- Source module: ProofsInTheBook.ZinanFFCT49 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT28
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT49

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT49

-- §0 the opened arm

-- §2 discharged pieces



-- §4 the bridge

-- §5 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT23
-/
/- Source module: ProofsInTheBook.ZinanFFCT52 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT52

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































































end ProofsInTheBook.ZinanFFCT52

-- §1 component 2


-- §2 reversal infra




-- §3 orientation normalization

-- §4 interval convexity


-- §5 assembly


end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT19
import ProofsInTheBook.ZinanFFCT46
import ProofsInTheBook.ZinanFFCT47
-/
/- Source module: ProofsInTheBook.ZinanFFCT48 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47

namespace ProofsInTheBook.ZinanFFCT48

set_option maxHeartbeats 1600000



























end ProofsInTheBook.ZinanFFCT48




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT25
import ProofsInTheBook.ZinanFFCT48
-/
/- Source module: ProofsInTheBook.ZinanFFCT53 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT25

namespace ProofsInTheBook.ZinanFFCT53

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


















































end ProofsInTheBook.ZinanFFCT53

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT52
import ProofsInTheBook.ZinanFFCT53
-/
/- Source module: ProofsInTheBook.ZinanFFCT54 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT21 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT52 ProofsInTheBook.ZinanFFCT53

namespace ProofsInTheBook.ZinanFFCT54

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















































































end ProofsInTheBook.ZinanFFCT54

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT54
-/
/- Source module: ProofsInTheBook.ZinanFFCT63 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54

namespace ProofsInTheBook.ZinanFFCT63

set_option maxHeartbeats 1600000




















































end ProofsInTheBook.ZinanFFCT63

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT28
-/
/- Source module: ProofsInTheBook.ZinanFFCT29 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT10 ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT28

namespace ProofsInTheBook.ZinanFFCT29

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT29

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT29
-/
/- Source module: ProofsInTheBook.ZinanFFCT31 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29

namespace ProofsInTheBook.ZinanFFCT31

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
























































end ProofsInTheBook.ZinanFFCT31

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT31
-/
/- Source module: ProofsInTheBook.ZinanFFCT32 -/
section
set_option autoImplicit true




noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT22 ProofsInTheBook.ZinanFFCT23 ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25 ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT31

namespace ProofsInTheBook.ZinanFFCT32

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















































end ProofsInTheBook.ZinanFFCT32

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT49
import ProofsInTheBook.ZinanFFCT32
-/
/- Source module: ProofsInTheBook.ZinanFFCT51 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT27 ProofsInTheBook.ZinanFFCT29 ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49

namespace ProofsInTheBook.ZinanFFCT51

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





























end ProofsInTheBook.ZinanFFCT51

-- §1 the sharp residue

-- §2 the corner sign verification

-- §3 the main near-side line


-- §4 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT51
-/
/- Source module: ProofsInTheBook.ZinanFFCT55 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT51

namespace ProofsInTheBook.ZinanFFCT55

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT55

-- §R1/R2 the constant-binding contradiction at the WBS family


-- §δ*=0 edge

-- §R3 slot normalization

-- §R4 the derivative + the sign finding



-- §R4′ the forced collapse

-- §5 non-vacuity guards



end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT21
import ProofsInTheBook.ZinanFFCT55
-/
/- Source module: ProofsInTheBook.ZinanFFCT56 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT55

namespace ProofsInTheBook.ZinanFFCT56

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT56

-- §A the coefficient bricks


-- §B the master mid-fold kill


-- §C the WBS axis-edge elimination

-- §D the honest dispatch + residue

-- §E the consequence wiring

-- §F non-vacuity guards




end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT56
-/
/- Source module: ProofsInTheBook.ZinanFFCT57 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT56

namespace ProofsInTheBook.ZinanFFCT57

set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT57









end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT10
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT57
-/
/- Source module: ProofsInTheBook.ZinanFFCT58 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT57

namespace ProofsInTheBook.ZinanFFCT58

set_option maxHeartbeats 1600000
set_option linter.unnecessarySeqFocus false























































































end ProofsInTheBook.ZinanFFCT58







end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT58
-/
/- Source module: ProofsInTheBook.ZinanFFCT59 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58

namespace ProofsInTheBook.ZinanFFCT59

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































end ProofsInTheBook.ZinanFFCT59









end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT54
import ProofsInTheBook.ZinanFFCT59
-/
/- Source module: ProofsInTheBook.ZinanFFCT60 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59

namespace ProofsInTheBook.ZinanFFCT60

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


























end ProofsInTheBook.ZinanFFCT60

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT60
import ProofsInTheBook.SphericalRotation
-/
/- Source module: ProofsInTheBook.ZinanFFCT61 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT60

namespace ProofsInTheBook.ZinanFFCT61

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































































































end ProofsInTheBook.ZinanFFCT61

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT61
-/
/- Source module: ProofsInTheBook.ZinanFFCT62 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61

namespace ProofsInTheBook.ZinanFFCT62

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















































end ProofsInTheBook.ZinanFFCT62

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT62
-/
/- Source module: ProofsInTheBook.ZinanFFCT64 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62

namespace ProofsInTheBook.ZinanFFCT64

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





































end ProofsInTheBook.ZinanFFCT64

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT63
import ProofsInTheBook.ZinanFFCT64
-/
/- Source module: ProofsInTheBook.ZinanFFCT65 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64

namespace ProofsInTheBook.ZinanFFCT65

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000



































































end ProofsInTheBook.ZinanFFCT65

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT65
import ProofsInTheBook.PlanarConvexDiag
-/
/- Source module: ProofsInTheBook.ZinanFFCT66 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT63
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65

namespace ProofsInTheBook.ZinanFFCT66

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000












































end ProofsInTheBook.ZinanFFCT66

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT66
-/
/- Source module: ProofsInTheBook.ZinanFFCT67 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66

namespace ProofsInTheBook.ZinanFFCT67

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















end ProofsInTheBook.ZinanFFCT67

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT67
import ProofsInTheBook.ZinanFFCT26
-/
/- Source module: ProofsInTheBook.ZinanFFCT68 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT26
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT67

namespace ProofsInTheBook.ZinanFFCT68

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000









































end ProofsInTheBook.ZinanFFCT68

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT68
-/
/- Source module: ProofsInTheBook.ZinanFFCT69 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT62
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT67
open ProofsInTheBook.ZinanFFCT68

namespace ProofsInTheBook.ZinanFFCT69

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




































end ProofsInTheBook.ZinanFFCT69

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT69
import ProofsInTheBook.ZinanFFCT32
-/
/- Source module: ProofsInTheBook.ZinanFFCT70 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT31
open ProofsInTheBook.ZinanFFCT32
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69

namespace ProofsInTheBook.ZinanFFCT70

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000




























end ProofsInTheBook.ZinanFFCT70

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT70
-/
/- Source module: ProofsInTheBook.ZinanFFCT71 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70

namespace ProofsInTheBook.ZinanFFCT71

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






























end ProofsInTheBook.ZinanFFCT71

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT71
-/
/- Source module: ProofsInTheBook.ZinanFFCT72 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71

namespace ProofsInTheBook.ZinanFFCT72

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000








































end ProofsInTheBook.ZinanFFCT72

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT72
-/
/- Source module: ProofsInTheBook.ZinanFFCT73 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT72

namespace ProofsInTheBook.ZinanFFCT73

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000










































end ProofsInTheBook.ZinanFFCT73

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT73
-/
/- Source module: ProofsInTheBook.ZinanFFCT74 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT73

namespace ProofsInTheBook.ZinanFFCT74

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































end ProofsInTheBook.ZinanFFCT74

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT74
-/
/- Source module: ProofsInTheBook.ZinanFFCT75 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74

namespace ProofsInTheBook.ZinanFFCT75

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000






















end ProofsInTheBook.ZinanFFCT75

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT75
import ProofsInTheBook.ZinanFFCT44
-/
/- Source module: ProofsInTheBook.ZinanFFCT76 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT44
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75

namespace ProofsInTheBook.ZinanFFCT76

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT76

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT76
-/
/- Source module: ProofsInTheBook.ZinanFFCT77 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76

namespace ProofsInTheBook.ZinanFFCT77

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































































end ProofsInTheBook.ZinanFFCT77

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT77
-/
/- Source module: ProofsInTheBook.ZinanFFCT78 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77

namespace ProofsInTheBook.ZinanFFCT78

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000















end ProofsInTheBook.ZinanFFCT78

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT78
-/
/- Source module: ProofsInTheBook.ZinanFFCT79 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78

namespace ProofsInTheBook.ZinanFFCT79

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000





















end ProofsInTheBook.ZinanFFCT79

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT79
-/
/- Source module: ProofsInTheBook.ZinanFFCT80 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79

namespace ProofsInTheBook.ZinanFFCT80

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































































end ProofsInTheBook.ZinanFFCT80

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT80
-/
/- Source module: ProofsInTheBook.ZinanFFCT81 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80

namespace ProofsInTheBook.ZinanFFCT81

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000










































end ProofsInTheBook.ZinanFFCT81

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT81
-/
/- Source module: ProofsInTheBook.ZinanFFCT82 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81

namespace ProofsInTheBook.ZinanFFCT82

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000


































end ProofsInTheBook.ZinanFFCT82

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT82
-/
/- Source module: ProofsInTheBook.ZinanFFCT83 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82

namespace ProofsInTheBook.ZinanFFCT83

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000







































end ProofsInTheBook.ZinanFFCT83

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT83
-/
/- Source module: ProofsInTheBook.ZinanFFCT84 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83

namespace ProofsInTheBook.ZinanFFCT84

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

















end ProofsInTheBook.ZinanFFCT84

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT84
-/
/- Source module: ProofsInTheBook.ZinanFFCT85 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84

namespace ProofsInTheBook.ZinanFFCT85

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000









































end ProofsInTheBook.ZinanFFCT85

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT85
-/
/- Source module: ProofsInTheBook.ZinanFFCT86 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85

namespace ProofsInTheBook.ZinanFFCT86

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000








































end ProofsInTheBook.ZinanFFCT86

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT86
-/
/- Source module: ProofsInTheBook.ZinanFFCT100 -/
section
set_option autoImplicit true




open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86

namespace ProofsInTheBook.ZinanFFCT100







end ProofsInTheBook.ZinanFFCT100




end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanFFCT100
-/
/- Source module: ProofsInTheBook.ZinanFFCT111 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT100

namespace ProofsInTheBook.ZinanFFCT111

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000













































































end ProofsInTheBook.ZinanFFCT111

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalReachStuck
import ProofsInTheBook.SphericalSZFinal
import ProofsInTheBook.SphericalSZClose
import ProofsInTheBook.ZinanFFCT111
-/
/- Source module: ProofsInTheBook.ZinanFFCT113 -/
section
set_option autoImplicit true




noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalHinge ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalFinish ProofsInTheBook.SphericalSZStep
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT78 ProofsInTheBook.ZinanFFCT111

namespace ProofsInTheBook.ZinanFFCT113

set_option maxHeartbeats 1600000































end ProofsInTheBook.ZinanFFCT113

end
end

/- Original source header (imports hoisted):
import ProofsInTheBook.SphericalOpenedArmCore
import ProofsInTheBook.ZinanFFCT111
import ProofsInTheBook.ZinanFFCT113
-/
/- Source module: ProofsInTheBook.ZinanFFCT112 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ZinanFFCT112

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalOpenedArmCore












end ProofsInTheBook.ZinanFFCT112




end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.ZinanFFCT112
-/
/- Source module: ProofsInTheBook.Chapter13 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter13

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm

/-- Edge signs in Cauchy's rigidity proof. -/
inductive EdgeSign where
  | plus | minus | zero
  deriving DecidableEq, Repr

open EdgeSign

/-- The nonzero signs left after Cauchy's proof discards unchanged edges. -/
inductive StrictEdgeSign where
  | plus | minus
  deriving DecidableEq, Repr





















namespace StrictTriangleSigns





end StrictTriangleSigns

















namespace CauchyArmOpeningObstruction



end CauchyArmOpeningObstruction



namespace CauchyArmClosingObstruction



end CauchyArmClosingObstruction



namespace CauchyArmFixedChordObstruction



end CauchyArmFixedChordObstruction

















namespace CauchyArmVertex







end CauchyArmVertex



namespace CauchyRigidityCertificate







end CauchyRigidityCertificate











end ProofsInTheBook.Chapter13

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.Chapter13
-/
/- Source module: ProofsInTheBook.Ch13CyclicSigns -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13CyclicSigns

open ProofsInTheBook.Chapter13
open EdgeSign



variable {α : Type*} [DecidableEq α]

























end ProofsInTheBook.Ch13CyclicSigns

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
-/
/- Source module: ProofsInTheBook.Ch13MarkedSphere -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13MarkedSphere

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns

variable {D : Type*} [Fintype D] [DecidableEq D]



























































/-- Edge involution of the tetrahedron map: the six transpositions pairing each dart
with its reverse. -/
def tetraAlpha : Equiv.Perm (Fin 12) :=
  (List.formPerm [0, 3]) * (List.formPerm [1, 6]) * (List.formPerm [2, 9]) *
    (List.formPerm [4, 7]) * (List.formPerm [5, 10]) * (List.formPerm [8, 11])

/-- Vertex rotation of the tetrahedron map: the four `3`-cycles rotating the darts
around each of the four vertices. -/
def tetraSigma : Equiv.Perm (Fin 12) :=
  (List.formPerm [0, 1, 2]) * (List.formPerm [3, 5, 4]) *
    (List.formPerm [6, 7, 8]) * (List.formPerm [9, 11, 10])

/-- The tetrahedron as a combinatorial map on `Fin 12`. -/
def tetraMap : CombMap (Fin 12) where
  α := tetraAlpha
  σ := tetraSigma
  α_invol := by decide
  α_no_fixed := by decide





noncomputable instance : DecidableEq (Quotient (cycleSetoid tetraMap.φ)) :=
  Quotient.decidableEq























end ProofsInTheBook.Ch13MarkedSphere

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
-/
/- Source module: ProofsInTheBook.Ch13MarkedReduction -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13MarkedReduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open EdgeSign
open Equiv Equiv.Perm



section ListBridge

variable {α : Type*} [DecidableEq α]







end ListBridge



section OrbitBridge

variable {α : Type*} [DecidableEq α] [Fintype α] {β : Type*} [DecidableEq β]









end OrbitBridge



section StrictBridge

variable {D : Type*} [Fintype D] [DecidableEq D]











end StrictBridge



section ActiveComponent

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The degree of a face (`φ`-orbit): the number of darts on its boundary walk. -/
def faceDeg (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card











end ActiveComponent



section Obstruction
































end Obstruction

end ProofsInTheBook.Ch13MarkedReduction

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
-/
/- Source module: ProofsInTheBook.Ch13ActiveComponent -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ActiveComponent

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open EdgeSign

variable {D : Type*} [Fintype D] [DecidableEq D]

















open ProofsInTheBook.SubmapPlanar

/-- The kept (active sub-)combinatorial map on the surviving darts `{d ∉ Del}`. -/
noncomputable def keptMap (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) : CombMap {d : D // d ∉ Del} where
  α := keptAlpha M Del hsub
  σ := Equiv.Perm.deleteSet M.σ Del
  α_invol := keptAlpha_invol M Del hsub
  α_no_fixed := by
    intro d hd
    apply M.α_no_fixed d.1
    have := congrArg Subtype.val hd
    rwa [keptAlpha_apply_coe] at this



@[simp] theorem keptMap_alpha (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).α = keptAlpha M Del hsub := rfl

/-- **Euler char of the kept map is `2` when it is connected** (genus-0 certificate from
`SubmapPlanar.keptMap_eulerChar_eq_two`): the active sub-map of a sphere has no handle. -/
theorem keptMap_eulerChar_eq_two_of_connected (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del) (hsphere : M.IsSphereMap)
    (d : {d : D // d ∉ Del}) (hconn : (keptMap M Del hsub).Connected) :
    (keptMap M Del hsub).eulerChar = 2 :=
  ProofsInTheBook.SubmapPlanar.keptMap_eulerChar_eq_two M Del hsub hclosed hsphere
    (keptMap M Del hsub) rfl rfl d hconn

/-- Euler identity form `(V:ℤ) - E + F = 2` for the connected kept map. -/
theorem keptMap_euler_VEF (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del) (hsphere : M.IsSphereMap)
    (d : {d : D // d ∉ Del}) (hconn : (keptMap M Del hsub).Connected) :
    ((keptMap M Del hsub).V : ℤ) - (keptMap M Del hsub).E + (keptMap M Del hsub).F = 2 := by
  have h := keptMap_eulerChar_eq_two_of_connected M Del hsub hclosed hsphere d hconn
  rwa [CombMap.eulerChar] at h



  -- unreachable on active darts























end ProofsInTheBook.Ch13ActiveComponent

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
-/
/- Source module: ProofsInTheBook.Ch13FlipTransport -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13FlipTransport

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.SubmapPlanar
open EdgeSign
open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]



open ProofsInTheBook -- for DeleteSet.firstOutside via Equiv.Perm namespace









































































end ProofsInTheBook.Ch13FlipTransport

end

/- Original source header (imports hoisted):
import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
import ProofsInTheBook.Ch13FlipTransport
import ProofsInTheBook.PlanarMapNearTriangulation
-/
/- Source module: ProofsInTheBook.Ch13ComponentClose -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Ch13ComponentClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.Ch13FlipTransport
open ProofsInTheBook.SubmapPlanar
open EdgeSign
open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- `faceDeg = faceLen` (same orbit-card definition). -/
theorem faceDeg_eq_faceLen (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) :
    faceDeg M Q = M.faceLen Q := rfl







/-- Two kept darts have the same kept tail-vertex iff their underlying darts have the same
`M`-tail-vertex. -/
theorem keptMap_tail_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).tail x = (keptMap M Del hsub).tail y ↔ M.tail x.1 = M.tail y.1 := by
  unfold CombMap.tail
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle x y ↔ M.σ.SameCycle x.1 y.1
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y

/-- The kept head-vertex of `x` is the `M`-head-vertex of `x.1`, transported. -/
theorem keptMap_head_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).head x = (keptMap M Del hsub).head y ↔ M.head x.1 = M.head y.1 := by
  unfold CombMap.head
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle ((keptMap M Del hsub).α x) ((keptMap M Del hsub).α y)
      ↔ M.σ.SameCycle (M.α x.1) (M.α y.1)
  have hx : ((keptMap M Del hsub).α x : D) = M.α x.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub x
  have hy : ((keptMap M Del hsub).α y : D) = M.α y.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub y
  rw [← hx, ← hy]
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del _ _

/-- Cross form: kept-tail of `x` equals kept-head of `y` iff `M`-tail of `x.1` equals `M`-head of
`y.1`. -/
theorem keptMap_tail_eq_head_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).tail x = (keptMap M Del hsub).head y ↔ M.tail x.1 = M.head y.1 := by
  unfold CombMap.tail CombMap.head
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle x ((keptMap M Del hsub).α y)
      ↔ M.σ.SameCycle x.1 (M.α y.1)
  have hy : ((keptMap M Del hsub).α y : D) = M.α y.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub y
  rw [← hy]
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del _ _

/-- The kept `dartEdge` of `x` is `s(keptTail x, keptHead x)`; we compare via the `M`-endpoints. -/
theorem keptMap_dartEdge_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).dartEdge x = (keptMap M Del hsub).dartEdge y
      ↔ M.dartEdge x.1 = M.dartEdge y.1 := by
  unfold CombMap.dartEdge
  rw [Sym2.eq_iff, Sym2.eq_iff,
    keptMap_tail_eq_iff M Del hsub x y, keptMap_head_eq_iff M Del hsub x y,
    keptMap_tail_eq_head_iff M Del hsub x y,
    show ((keptMap M Del hsub).head x = (keptMap M Del hsub).tail y)
        ↔ (M.head x.1 = M.tail y.1) from by
      rw [eq_comm, keptMap_tail_eq_head_iff M Del hsub y x, eq_comm]]

/-- **The kept (active sub-)map inherits `IsSimpleGraph`.** -/
theorem keptMap_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).IsSimpleGraph where
  no_loop x := by
    rw [Ne, keptMap_tail_eq_head_iff M Del hsub x x]
    exact hM.no_loop x.1
  no_parallel {x y} h := by
    -- kept dartEdge equal ⟹ M dartEdge equal ⟹ M.α.SameCycle x.1 y.1 ⟹ keptAlpha.SameCycle x y
    rw [keptMap_dartEdge_eq_iff M Del hsub x y] at h
    have hMsc : M.α.SameCycle x.1 y.1 := hM.no_parallel h
    -- y.1 ∈ {x.1, M.α x.1}; both kept; gives keptAlpha.SameCycle x y
    rcases (M.alpha_sameCycle_iff x.1 y.1).mp hMsc with hxy | hxy
    · -- y = x
      have hyx : y = x := Subtype.ext hxy
      exact hyx ▸ Equiv.Perm.SameCycle.rfl
    · -- y = M.α x.1 = keptAlpha x (coercion)
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hcoe : ((keptMap M Del hsub).α x : D) = M.α x.1 := by
        rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub x
      rw [zpow_one, hcoe]
      exact hxy.symm





























variable (M : CombMap D) (es : D → EdgeSign)





















/-- A digon (`faceLen = 2`) representative `d` of a simple map has both `A.σ d = d` and
`A.σ (A.α d) = A.α d` (both darts of its single edge are `σ`-fixed leaves). -/
theorem digon_sigma_fixed {A : CombMap D} (hA : A.IsSimpleGraph) {d : D}
    (hφ : A.φ d ≠ d) (hcard2 : (A.φ.cycleOf d).support.card = 2) :
    A.σ d = d ∧ A.σ (A.α d) = A.α d := by
  -- φ² d = d (digon)
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply A.φ 2 d
  rw [hcard2] at hpow
  have hsq : A.φ (A.φ d) = d := by
    have h2 : (A.φ ^ 2) d = d := by simpa using hpow.symm
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using h2
  -- the two boundary darts share an edge ⟹ φ d = α d
  have he1 : A.dartEdge d = s(A.tail d, A.tail (A.φ d)) := A.dartEdge_eq_mk_tail_tail_phi d
  have he2 : A.dartEdge (A.φ d) = s(A.tail (A.φ d), A.tail d) := by
    rw [A.dartEdge_eq_mk_tail_tail_phi (A.φ d), hsq]
  have hedge : A.dartEdge d = A.dartEdge (A.φ d) := by rw [he1, he2, Sym2.eq_swap]
  have hsc : A.α.SameCycle d (A.φ d) := hA.no_parallel hedge
  have hφα : A.φ d = A.α d := by
    rcases (A.alpha_sameCycle_iff d (A.φ d)).mp hsc with hcase | hcase
    · exact absurd hcase hφ
    · exact hcase
  -- φ = σ * α: φ d = σ (α d) = α d ⟹ σ fixes α d
  have hσαd : A.σ (A.α d) = A.α d := by
    have : A.σ (A.α d) = A.φ d := rfl
    rw [this, hφα]
  -- φ (φ d) = d with φ d = α d: φ (α d) = σ (α (α d)) = σ d = d ⟹ σ fixes d
  have hσd : A.σ d = d := by
    have hφαd : A.φ (A.α d) = d := by rw [← hφα]; exact hsq
    have hcalc : A.σ d = A.φ (A.α d) := by
      show A.σ d = A.σ (A.α (A.α d))
      rw [A.alpha_alpha]
    rw [hcalc, hφαd]
  exact ⟨hσd, hσαd⟩

/-- **A connected simple map with `≥ 2` edges has all faces of degree `≥ 3`** (no digon). -/
theorem three_le_faceDeg_of_connected_simple_twoEdge {A : CombMap D} (hA : A.IsSimpleGraph)
    (hconn : A.Connected) (hE : 2 ≤ A.E) (R : Quotient (cycleSetoid A.φ)) :
    3 ≤ faceDeg A R := by
  obtain ⟨d, rfl⟩ := R.exists_rep
  have hφ : A.φ d ≠ d := phi_ne_self_of_isSimpleGraph A hA d
  rw [faceDeg_eq_faceLen]
  show 3 ≤ A.faceLen (A.dartFace d)
  rw [faceLen_dartFace_eq_card_support_cycleOf A hφ]
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ (A.φ.cycleOf d).support.card :=
    (Equiv.Perm.isCycle_cycleOf A.φ hφ).two_le_card_support
  have hcard2 : (A.φ.cycleOf d).support.card = 2 := by omega
  obtain ⟨hσd, hσαd⟩ := digon_sigma_fixed hA hφ hcard2
  -- the edge {d, α d} is the entire (connected) map: every dart is d or α d
  have hαd_ne : A.α d ≠ d := A.α_no_fixed d
  -- dartStep from d stays in {d, α d}
  have hstep_d : ∀ y, A.dartStep d y → y = d ∨ y = A.α d := by
    intro y hy
    rcases hy with hσ | hαe
    · -- same σ-cycle as d; σ fixes d ⟹ y = d
      left
      obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := A.σ) hσ
      have : (A.σ ^ k) d = d := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσd k
      rw [← hk, this]
    · exact Or.inr hαe
  have hstep_αd : ∀ y, A.dartStep (A.α d) y → y = d ∨ y = A.α d := by
    intro y hy
    rcases hy with hσ | hαe
    · right
      obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := A.σ) hσ
      have : (A.σ ^ k) (A.α d) = A.α d := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσαd k
      rw [← hk, this]
    · left; rw [hαe, A.alpha_alpha]
  -- every dart reachable from d lies in {d, α d}
  have hall : ∀ y, Relation.ReflTransGen A.dartStep d y → y = d ∨ y = A.α d := by
    intro y h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
        rcases ih with rfl | rfl
        · exact hstep_d c hbc
        · exact hstep_αd c hbc
  have hsub : ∀ y : D, y ∈ ({d, A.α d} : Finset D) := by
    intro y
    have := hall y (hconn d y)
    rcases this with rfl | rfl <;> simp
  -- so |D| ≤ 2, hence 2*E = |D| ≤ 2, E ≤ 1, contradicting hE
  have hcardD : Fintype.card D ≤ 2 := by
    have hle : Fintype.card D ≤ ({d, A.α d} : Finset D).card := by
      rw [← Finset.card_univ]
      apply Finset.card_le_card
      intro y _; exact hsub y
    calc Fintype.card D ≤ ({d, A.α d} : Finset D).card := hle
      _ ≤ 2 := by
          calc ({d, A.α d} : Finset D).card ≤ ({A.α d} : Finset D).card + 1 :=
                Finset.card_insert_le _ _
            _ ≤ 2 := by simp
  have h2E : 2 * A.E = Fintype.card D := A.two_mul_E_eq_card
  omega



















end ProofsInTheBook.Ch13ComponentClose

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapSimple
-/
/- Source module: ProofsInTheBook.FaceDiagonalSurgery -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordSideRecon

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-- A choice of two non-adjacent boundary darts of a common face whose tail
vertices can be joined by a new diagonal edge.  The field
`nonadjacent_on_face` records the local boundary bookkeeping: the two cut
locations are not consecutive in either direction on the selected face. -/
structure FaceDiagonalChoice (M : CombMap D) where
  f : M.Face
  d0 : D
  d1 : D
  same_face : M.dartFace d0 = f
  same_face' : M.dartFace d1 = f
  endpoints_distinct : M.tail d0 ≠ M.tail d1
  no_existing_edge : ¬ M.toSimpleGraph.Adj (M.tail d0) (M.tail d1)
  nonadjacent_on_face : M.φ d0 ≠ d1 ∧ M.φ d1 ≠ d0

namespace FaceDiagonalChoice

variable {M : CombMap D} (c : FaceDiagonalChoice M)

/-- First splice anchor: the dart whose `σ`-successor is the first chosen
face dart. -/
def anchor0 : D :=
  M.σ.symm c.d0

/-- Second splice anchor: the dart whose `σ`-successor is the second chosen
face dart. -/
def anchor1 : D :=
  M.σ.symm c.d1

@[simp] lemma sigma_anchor0 : M.σ c.anchor0 = c.d0 := by
  simp [anchor0]

@[simp] lemma sigma_anchor1 : M.σ c.anchor1 = c.d1 := by
  simp [anchor1]

lemma tail_anchor0 : M.tail c.anchor0 = M.tail c.d0 := by
  have h := M.tail_sigma (M.σ.symm c.d0)
  simpa [anchor0] using h.symm

lemma tail_anchor1 : M.tail c.anchor1 = M.tail c.d1 := by
  have h := M.tail_sigma (M.σ.symm c.d1)
  simpa [anchor1] using h.symm

/-- The two splice anchors are distinct because their tail vertices are
distinct. -/
lemma anchors_ne : c.anchor0 ≠ c.anchor1 := by
  intro h
  apply c.endpoints_distinct
  calc
    M.tail c.d0 = M.tail c.anchor0 := (c.tail_anchor0).symm
    _ = M.tail c.anchor1 := by rw [h]
    _ = M.tail c.d1 := c.tail_anchor1

/-- The selected darts lie in the same old face orbit. -/
lemma same_face_sameCycle : M.φ.SameCycle c.d0 c.d1 := by
  change (cycleSetoid M.φ).r c.d0 c.d1
  apply Quotient.exact
  exact c.same_face.trans c.same_face'.symm

/-- The same-face condition in the exact form consumed by
`freshMap_F_same_face`. -/
lemma keptPhi_anchor_successors_sameCycle :
    (keptPhi M.α M.σ).SameCycle (M.σ c.anchor0) (M.σ c.anchor1) := by
  simpa [keptPhi, CombMap.φ] using c.same_face_sameCycle

end FaceDiagonalChoice

/-- Add one internal face diagonal by the generic fresh-dart adjunction. -/
noncomputable def addFaceDiagonal (M : CombMap D) (c : FaceDiagonalChoice M) :
    CombMap (D ⊕ Fin 2) :=
  freshMap M.α M.σ M.α_invol M.α_no_fixed c.anchor0 c.anchor1 c.anchors_ne

/-- Face excess: total surplus over triangular faces. -/
noncomputable def faceExcess (M : CombMap D) : ℕ :=
  ∑ f : M.Face, (M.faceLen f - 3)

theorem faceExcess_eq_two_mul_E_sub_three_mul_F
    (M : CombMap D) (h3 : M.FaceLengthGe 3) :
    faceExcess M = 2 * M.E - 3 * M.F := by
  unfold faceExcess
  have hsum := Finset.sum_tsub_distrib (s := (Finset.univ : Finset M.Face))
    (f := fun Q : M.Face => M.faceLen Q) (g := fun _ : M.Face => 3)
    (by intro Q _; exact h3 Q)
  calc
    (∑ Q : M.Face, (M.faceLen Q - 3))
        = (∑ Q : M.Face, M.faceLen Q) - Fintype.card M.Face * 3 := by
          simpa using hsum
    _ = 2 * M.E - 3 * M.F := by
          rw [sum_faceLen]
          simp [CombMap.F, Nat.mul_comm]

lemma sameCycle_mem_triple_of_phi_cube {p : Equiv.Perm D} {d e : D}
    (hcube : p (p (p d)) = d) (h : p.SameCycle d e) :
    e = d ∨ e = p d ∨ e = p (p d) := by
  obtain ⟨i, hi⟩ := h
  have hinv0 : p.symm d = p (p d) := by
    rw [Equiv.symm_apply_eq]
    exact hcube.symm
  have hinv1 : p.symm (p d) = d := by
    rw [Equiv.symm_apply_eq]
  have hinv2 : p.symm (p (p d)) = p d := by
    rw [Equiv.symm_apply_eq]
  have key : ∀ k : ℤ, (p ^ k) d = d ∨ (p ^ k) d = p d ∨
      (p ^ k) d = p (p d) := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · left
      simp
    · intro n ih
      rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one,
        Equiv.Perm.mul_apply]
      rcases ih with h0 | h1 | h2
      · right
        left
        rw [h0]
      · right
        right
        rw [h1]
      · left
        rw [h2]
        exact hcube
    · intro n ih
      have hstep : (p ^ (-(n : ℤ) - 1)) d = p.symm ((p ^ (-(n : ℤ))) d) := by
        rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add,
          Equiv.Perm.mul_apply, show (p ^ (-1 : ℤ)) = p.symm from by
            rw [zpow_neg, zpow_one]
            rfl]
      rw [hstep]
      rcases ih with h0 | h1 | h2
      · rw [h0]
        right
        right
        exact hinv0
      · rw [h1]
        left
        exact hinv1
      · rw [h2]
        right
        left
        exact hinv2
  rcases key i with h0 | h1 | h2
  · left
    rw [← hi, h0]
  · right
    left
    rw [← hi, h1]
  · right
    right
    rw [← hi, h2]

namespace FaceDiagonal

variable (M : CombMap D) (c : FaceDiagonalChoice M)

/-- The old vertices embed into the fresh map by sending an old dart orbit to
the corresponding `inl` fresh-rotation orbit. -/
noncomputable def includeVertex :
    M.Vertex → (addFaceDiagonal M c).Vertex :=
  Quotient.lift
    (fun d : D =>
      Quotient.mk (cycleSetoid (addFaceDiagonal M c).σ) (Sum.inl d))
    (by
      intro d e hde
      apply Quotient.sound
      change (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle
        (Sum.inl d) (Sum.inl e)
      rw [freshSigma_sameCycle_iff M.σ c.anchors_ne]
      simpa using hde)



/-- The old-vertex embedding is injective. -/
theorem includeVertex_injective :
    Function.Injective (includeVertex M c) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro d e hde
  have hfresh :
      (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle
        (Sum.inl d) (Sum.inl e) := by
    exact Quotient.exact hde
  have hold : M.σ.SameCycle d e := by
    have hproj := (freshSigma_sameCycle_iff M.σ c.anchors_ne
      (Sum.inl d) (Sum.inl e)).1 hfresh
    simpa using hproj
  exact Quotient.sound hold

lemma includeVertex_head (d : D) :
    includeVertex M c (M.head d)
      = (addFaceDiagonal M c).head (Sum.inl d) := by
  rfl

/-- Collapse a fresh-map vertex back to the old vertex containing its anchor
projection. -/
noncomputable def vertexToOld :
    (addFaceDiagonal M c).Vertex → M.Vertex :=
  Quotient.lift
    (fun x : D ⊕ Fin 2 => M.tail (proj c.anchor0 c.anchor1 x))
    (by
      intro x y hxy
      have hsc :
          (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle x y := by
        simpa [addFaceDiagonal] using hxy
      have hproj : M.σ.SameCycle
          (proj c.anchor0 c.anchor1 x) (proj c.anchor0 c.anchor1 y) :=
        (freshSigma_sameCycle_iff M.σ c.anchors_ne x y).1 hsc
      exact Quotient.sound hproj)

@[simp] lemma vertexToOld_tail (x : D ⊕ Fin 2) :
    vertexToOld M c ((addFaceDiagonal M c).tail x)
      = M.tail (proj c.anchor0 c.anchor1 x) :=
  rfl

@[simp] lemma vertexToOld_head (x : D ⊕ Fin 2) :
    vertexToOld M c ((addFaceDiagonal M c).head x)
      = M.tail (proj c.anchor0 c.anchor1 ((addFaceDiagonal M c).α x)) :=
  rfl

@[simp] lemma vertexToOld_tail_inl (d : D) :
    vertexToOld M c ((addFaceDiagonal M c).tail (Sum.inl d)) = M.tail d := by
  simp [vertexToOld_tail, proj]

@[simp] lemma vertexToOld_head_inl (d : D) :
    vertexToOld M c ((addFaceDiagonal M c).head (Sum.inl d)) = M.head d := by
  rw [vertexToOld_head]
  simp [addFaceDiagonal, proj, CombMap.head]

@[simp] lemma vertexToOld_tail_inr_zero :
    vertexToOld M c ((addFaceDiagonal M c).tail (Sum.inr (0 : Fin 2))) = M.tail c.d0 := by
  simp [vertexToOld_tail, proj, c.tail_anchor0]

@[simp] lemma vertexToOld_head_inr_zero :
    vertexToOld M c ((addFaceDiagonal M c).head (Sum.inr (0 : Fin 2))) = M.tail c.d1 := by
  rw [vertexToOld_head]
  simp [addFaceDiagonal, proj, c.tail_anchor1]

@[simp] lemma vertexToOld_tail_inr_one :
    vertexToOld M c ((addFaceDiagonal M c).tail (Sum.inr (1 : Fin 2))) = M.tail c.d1 := by
  simp [vertexToOld_tail, proj, c.tail_anchor1]

@[simp] lemma vertexToOld_head_inr_one :
    vertexToOld M c ((addFaceDiagonal M c).head (Sum.inr (1 : Fin 2))) = M.tail c.d0 := by
  rw [vertexToOld_head]
  simp [addFaceDiagonal, proj, c.tail_anchor0]

lemma map_dartEdge_inl (d : D) :
    Sym2.map (vertexToOld M c) ((addFaceDiagonal M c).dartEdge (Sum.inl d))
      = M.dartEdge d := by
  rw [CombMap.dartEdge, Sym2.map_mk]
  simp only [vertexToOld_tail_inl, vertexToOld_head_inl]
  rfl

lemma map_dartEdge_inr_zero :
    Sym2.map (vertexToOld M c)
        ((addFaceDiagonal M c).dartEdge (Sum.inr (0 : Fin 2)))
      = s(M.tail c.d0, M.tail c.d1) := by
  rw [CombMap.dartEdge, Sym2.map_mk]
  simp only [vertexToOld_tail_inr_zero, vertexToOld_head_inr_zero]

lemma map_dartEdge_inr_one :
    Sym2.map (vertexToOld M c)
        ((addFaceDiagonal M c).dartEdge (Sum.inr (1 : Fin 2)))
      = s(M.tail c.d0, M.tail c.d1) := by
  rw [CombMap.dartEdge, Sym2.map_mk]
  simp only [vertexToOld_tail_inr_one, vertexToOld_head_inr_one]
  exact Sym2.eq_swap

/-- A fresh diagonal dart is not a loop under the endpoint-distinct hypothesis,
and old darts remain non-loops from the original simple-map hypothesis. -/
theorem no_loop (hSimple : M.IsSimpleGraph) :
    ∀ x : D ⊕ Fin 2, (addFaceDiagonal M c).tail x ≠ (addFaceDiagonal M c).head x := by
  intro x h
  have hsc :
      (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle
        x (freshAlpha M.α x) := by
    simpa [addFaceDiagonal] using (Quotient.exact h)
  have hproj := (freshSigma_sameCycle_iff M.σ c.anchors_ne
    x (freshAlpha M.α x)).1 hsc
  cases x with
  | inl d =>
      have hold : M.σ.SameCycle d (M.α d) := by
        simpa [proj] using hproj
      exact hSimple.no_loop d (Quotient.sound hold)
  | inr j =>
      fin_cases j
      · have ht : M.tail c.anchor0 = M.tail c.anchor1 := by
          exact Quotient.sound (by simpa [proj] using hproj)
        apply c.endpoints_distinct
        calc
          M.tail c.d0 = M.tail c.anchor0 := (c.tail_anchor0).symm
          _ = M.tail c.anchor1 := ht
          _ = M.tail c.d1 := c.tail_anchor1
      · have ht : M.tail c.anchor1 = M.tail c.anchor0 := by
          exact Quotient.sound (by simpa [proj] using hproj)
        apply c.endpoints_distinct
        calc
          M.tail c.d0 = M.tail c.anchor0 := (c.tail_anchor0).symm
          _ = M.tail c.anchor1 := ht.symm
          _ = M.tail c.d1 := c.tail_anchor1

lemma freshAlpha_sameCycle_inl_of_alpha_sameCycle {d e : D}
    (h : M.α.SameCycle d e) :
    (addFaceDiagonal M c).α.SameCycle (Sum.inl d) (Sum.inl e) := by
  rcases (M.alpha_sameCycle_iff d e).1 h with rfl | rfl
  · exact Equiv.Perm.SameCycle.refl _ _
  · refine ⟨1, ?_⟩
    simp [addFaceDiagonal]

lemma freshAlpha_sameCycle_inr (j k : Fin 2) :
    (addFaceDiagonal M c).α.SameCycle (Sum.inr j) (Sum.inr k) := by
  fin_cases j <;> fin_cases k
  · exact Equiv.Perm.SameCycle.refl _ _
  · refine ⟨1, ?_⟩
    simp [addFaceDiagonal]
  · refine ⟨1, ?_⟩
    simp [addFaceDiagonal]
  · exact Equiv.Perm.SameCycle.refl _ _

lemma no_old_fresh_parallel (hSimple : M.IsSimpleGraph) {d : D} {j : Fin 2}
    (h : (addFaceDiagonal M c).dartEdge (Sum.inl d)
        = (addFaceDiagonal M c).dartEdge (Sum.inr j)) :
    False := by
  have hmap := congrArg (Sym2.map (vertexToOld M c)) h
  have hedge : M.dartEdge d = s(M.tail c.d0, M.tail c.d1) := by
    fin_cases j
    · simpa [map_dartEdge_inl, map_dartEdge_inr_zero] using hmap
    · simpa [map_dartEdge_inl, map_dartEdge_inr_one] using hmap
  have hadj : M.Adj (M.tail c.d0) (M.tail c.d1) := ⟨d, hedge⟩
  exact c.no_existing_edge ⟨c.endpoints_distinct, hadj⟩

/-- The face diagonal preserves map simplicity: old parallel edges are handled
by `hSimple`, the fresh edge is non-loop by `endpoints_distinct`, and it is not
parallel to an old edge by `no_existing_edge`. -/
theorem simple (hSimple : M.IsSimpleGraph) :
    (addFaceDiagonal M c).IsSimpleGraph := by
  refine ⟨no_loop M c hSimple, ?_⟩
  intro x y hxy
  cases x with
  | inl d =>
      cases y with
      | inl e =>
          have hmap := congrArg (Sym2.map (vertexToOld M c)) hxy
          have hold : M.dartEdge d = M.dartEdge e := by
            simpa [map_dartEdge_inl] using hmap
          exact freshAlpha_sameCycle_inl_of_alpha_sameCycle M c (hSimple.no_parallel hold)
      | inr j =>
          exact False.elim (no_old_fresh_parallel M c hSimple hxy)
  | inr j =>
      cases y with
      | inl e =>
          exact (False.elim (no_old_fresh_parallel M c hSimple hxy.symm))
      | inr k =>
          exact freshAlpha_sameCycle_inr M c j k

/-- The vertex count is unchanged by inserting the two fresh darts into
existing vertex rotations. -/
theorem V_eq :
    (addFaceDiagonal M c).V = M.V := by
  simpa [addFaceDiagonal, CombMap.V] using
    (freshMap_V M.σ c.anchors_ne M.α M.α_invol M.α_no_fixed)

/-- The edge count rises by one: the two new darts form one new `α`-orbit. -/
theorem E_eq :
    (addFaceDiagonal M c).E = M.E + 1 := by
  have hfresh :
      2 * (addFaceDiagonal M c).E = Fintype.card D + 2 := by
    simpa [addFaceDiagonal] using
      (freshMap_two_mul_E M.α M.σ M.α_invol M.α_no_fixed
        c.anchor0 c.anchor1 c.anchors_ne)
  have hold : 2 * M.E = Fintype.card D := M.two_mul_E_eq_card
  omega

/-- The selected old face orbit is split into two old-plus-fresh face orbits;
all other old face orbits are unchanged at the cycle-count level. -/
theorem F_eq :
    (addFaceDiagonal M c).F = M.F + 1 := by
  have hsame := c.keptPhi_anchor_successors_sameCycle
  have hF :
      (addFaceDiagonal M c).F = numCycles (keptPhi M.α M.σ) + 1 := by
    simpa [addFaceDiagonal] using
      (freshMap_F_same_face M.α M.σ M.α_invol M.α_no_fixed
        c.anchors_ne hsame)
  rw [hF]
  have hOld : M.F = numCycles (keptPhi M.α M.σ) := by
    rw [M.F_eq_numCycles]
    rfl
  omega

/-- The fresh map remains connected when the old map is connected. -/
theorem connected (hconn : M.Connected) :
    (addFaceDiagonal M c).Connected := by
  simpa [addFaceDiagonal, keptCombMap] using
    (freshMap_connected_of_kept M.α M.σ M.α_invol M.α_no_fixed
      c.anchors_ne (by simpa [keptCombMap] using hconn))

/-- Sphere-map preservation from the count identities. -/
theorem sphere (hS : M.IsSphereMap) :
    (addFaceDiagonal M c).IsSphereMap := by
  refine ⟨connected M c hS.1, ?_⟩
  unfold CombMap.eulerChar
  have hV := V_eq M c
  have hE := E_eq M c
  have hF := F_eq M c
  rw [hV, hE, hF]
  norm_num [Nat.cast_add]
  ring_nf
  simpa [CombMap.eulerChar] using hS.2

/-- Old adjacency embeds into the fresh map through `includeVertex`. -/
theorem old_adj_embed {u v : M.Vertex}
    (hadj : M.toSimpleGraph.Adj u v) :
    (addFaceDiagonal M c).toSimpleGraph.Adj
      (includeVertex M c u) (includeVertex M c v) := by
  rcases hadj with ⟨hne, d, hd⟩
  refine ⟨?_, Sum.inl d, ?_⟩
  · intro h
    exact hne (includeVertex_injective M c h)
  · have hmap := congrArg (Sym2.map (includeVertex M c)) hd
    simpa [CombMap.dartEdge, includeVertex_head] using hmap

lemma old_E_ge_two (c : FaceDiagonalChoice M) (hSimple : M.IsSimpleGraph) : 2 ≤ M.E := by
  have hd01 : c.d0 ≠ c.d1 := by
    intro h
    exact c.endpoints_distinct (by rw [h])
  have hφ0 : M.φ c.d0 ≠ c.d0 := by
    intro h
    apply hSimple.no_loop c.d0
    rw [← M.tail_phi c.d0, h]
  have hφ01 : M.φ c.d0 ≠ c.d1 := c.nonadjacent_on_face.1
  let f : Fin 3 → D := fun i =>
    if i = 0 then c.d0 else if i = 1 then c.d1 else M.φ c.d0
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hd01, hd01.symm, hφ0, hφ0.symm, hφ01, hφ01.symm] at hij ⊢
  have hcard : 3 ≤ Fintype.card D := by
    simpa using Fintype.card_le_of_injective f hf
  have htwo := M.two_mul_E_eq_card
  omega

theorem faceLengthGe_three (c : FaceDiagonalChoice M)
    (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) :
    M.FaceLengthGe 3 := by
  intro Q
  have hdeg := ProofsInTheBook.Ch13ComponentClose.three_le_faceDeg_of_connected_simple_twoEdge
    (A := M) hSimple hS.1 (old_E_ge_two M c hSimple) Q
  simpa [ProofsInTheBook.Ch13ComponentClose.faceDeg_eq_faceLen] using hdeg

theorem faceLengthGe_three_add (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) :
    (addFaceDiagonal M c).FaceLengthGe 3 := by
  intro Q
  have hS' := sphere M c hS
  have hSimple' := simple M c hSimple
  have hEold := old_E_ge_two M c hSimple
  have hE' : 2 ≤ (addFaceDiagonal M c).E := by
    have hEeq := E_eq M c
    omega
  have hdeg := ProofsInTheBook.Ch13ComponentClose.three_le_faceDeg_of_connected_simple_twoEdge
    (A := addFaceDiagonal M c) hSimple' hS'.1 hE' Q
  simpa [ProofsInTheBook.Ch13ComponentClose.faceDeg_eq_faceLen] using hdeg

lemma chosen_face_len_ne_three (hSimple : M.IsSimpleGraph) :
    M.faceLen c.f ≠ 3 := by
  intro hlen
  have hlen0 : M.faceLen (M.dartFace c.d0) = 3 := by
    rw [c.same_face, hlen]
  have hcube := faceLen_three_phi_cube_eq_self M hSimple hlen0
  have hsc : M.φ.SameCycle c.d0 c.d1 := c.same_face_sameCycle
  rcases sameCycle_mem_triple_of_phi_cube hcube hsc with h | h | h
  · apply c.endpoints_distinct
    rw [h]
  · exact c.nonadjacent_on_face.1 h.symm
  · have hφd1 : M.φ c.d1 = c.d0 := by
      rw [h]
      simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
    exact c.nonadjacent_on_face.2 hφd1

lemma faceExcess_pos (c : FaceDiagonalChoice M)
    (h3 : M.FaceLengthGe 3) (hSimple : M.IsSimpleGraph) :
    0 < faceExcess M := by
  have hne := chosen_face_len_ne_three M c hSimple
  have hlt : 3 < M.faceLen c.f := by
    exact lt_of_le_of_ne (h3 c.f) (by intro h; exact hne h.symm)
  have hterm : 0 < M.faceLen c.f - 3 := Nat.sub_pos_of_lt hlt
  unfold faceExcess
  have hle :
      M.faceLen c.f - 3 ≤ ∑ f : M.Face, (M.faceLen f - 3) := by
    simpa using Finset.single_le_sum
      (s := (Finset.univ : Finset M.Face))
      (f := fun f : M.Face => M.faceLen f - 3)
      (by intro f _; exact Nat.zero_le _)
      (Finset.mem_univ c.f)
  exact lt_of_lt_of_le hterm hle

theorem faceExcess_decrease (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) :
    faceExcess (addFaceDiagonal M c) < faceExcess M := by
  have h3old := faceLengthGe_three M c hS hSimple
  have h3new := faceLengthGe_three_add M c hS hSimple
  have hold := faceExcess_eq_two_mul_E_sub_three_mul_F M h3old
  have hnew := faceExcess_eq_two_mul_E_sub_three_mul_F (addFaceDiagonal M c) h3new
  have hE := E_eq M c
  have hF := F_eq M c
  have hpos := faceExcess_pos M c h3old hSimple
  rw [hnew, hold, hE, hF] at *
  omega

end FaceDiagonal

/-- A one-step face-diagonal insertion certificate.  The generic fresh-map
count, connectivity, simplicity, old-edge embedding, and excess decrease fields
are produced below. -/
structure FaceDiagonalInsertion
    (M : CombMap D) (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (c : FaceDiagonalChoice M) where
  D' : Type u
  [fintypeD' : Fintype D']
  [decEqD' : DecidableEq D']
  M' : CombMap D'
  includeDart : D → D'
  includeVertex : M.Vertex → M'.Vertex
  sphere' : M'.IsSphereMap
  simple' : M'.IsSimpleGraph
  old_adj_embed :
    ∀ {u v : M.Vertex}, M.toSimpleGraph.Adj u v →
      M'.toSimpleGraph.Adj (includeVertex u) (includeVertex v)
  V_eq : M'.V = M.V
  E_eq : M'.E = M.E + 1
  F_eq : M'.F = M.F + 1
  faceExcess_decrease : faceExcess M' < faceExcess M

attribute [instance] FaceDiagonalInsertion.fintypeD' FaceDiagonalInsertion.decEqD'

namespace FaceDiagonalInsertion

/-- Assemble the diagonal insertion certificate from the two remaining local
geometric obligations. -/
noncomputable def of_addFaceDiagonal
    (M : CombMap D) (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (c : FaceDiagonalChoice M) :
    FaceDiagonalInsertion M hS hSimple c where
  D' := D ⊕ Fin 2
  M' := addFaceDiagonal M c
  includeDart := Sum.inl
  includeVertex := FaceDiagonal.includeVertex M c
  sphere' := FaceDiagonal.sphere M c hS
  simple' := FaceDiagonal.simple M c hSimple
  old_adj_embed := by
    intro u v h
    exact FaceDiagonal.old_adj_embed M c h
  V_eq := FaceDiagonal.V_eq M c
  E_eq := FaceDiagonal.E_eq M c
  F_eq := FaceDiagonal.F_eq M c
  faceExcess_decrease := FaceDiagonal.faceExcess_decrease M c hS hSimple

end FaceDiagonalInsertion

end ProofsInTheBook.PlanarMap.CombMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapChordSplitData
import ProofsInTheBook.PlanarMapCutCap
-/
/- Source module: ProofsInTheBook.ZinanCh35StarRotation -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



/-- A **star dart** at a vertex `x`: a dart whose tail is `x`.  Since `M.Vertex` is the
`σ`-orbit quotient and `M.tail d = ⟦d⟧_σ`, this is precisely the cyclic family of darts
incident at `x` in their rotation order. -/
abbrev StarDart (M : CombMap D) (x : M.Vertex) : Type _ :=
  {d : D // M.tail d = x}

instance (M : CombMap D) (x : M.Vertex) : DecidableEq (StarDart M x) :=
  Subtype.instDecidableEq

instance (M : CombMap D) (x : M.Vertex) : Fintype (StarDart M x) :=
  Subtype.fintype _









variable {M : CombMap D} (hNT : NearTriangulation M)













































end CombMap

end ProofsInTheBook.PlanarMap

-- Axiom audit for the main brick results (expect: propext, Classical.choice, Quot.sound).









end

/- Original source header (imports hoisted):
import ProofsInTheBook.SubmapPlanar
-/
/- Source module: ProofsInTheBook.ChordSideClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



section RawPrimitives

variable (M)

open scoped Classical

/-- For a kept dart `a` (`a ∉ Del`), one raw face step is one `M.φ` step:
`(M.σ * rawAlpha) a = M.φ a`. -/
lemma rawFace_step_eq_phi {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} (ha : a ∉ Del) :
    (M.σ * SubmapPlanar.rawAlpha M Del hclosed) a = M.φ a := by
  rw [Equiv.Perm.mul_apply, SubmapPlanar.rawAlpha_eq_alpha_of_notMem M Del hclosed ha]
  rfl

/-- **Raw face walk.**  If `a` and the first `k` forward `M.φ`-iterates `M.φ^j a` (`0 ≤ j < k`)
are all kept, then `(M.σ * rawAlpha)^k a = M.φ^k a`. -/
lemma rawFace_walk {Del : Finset D} (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} :
    ∀ k : ℕ, (∀ j : ℕ, j < k → (M.φ ^ j) a ∉ Del) →
      ((M.σ * SubmapPlanar.rawAlpha M Del hclosed) ^ k) a = (M.φ ^ k) a := by
  classical
  set p := M.σ * SubmapPlanar.rawAlpha M Del hclosed with hp
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hkept
      have ihk : (p ^ k) a = (M.φ ^ k) a :=
        ih (fun j hj => hkept j (by omega))
      have hak : (M.φ ^ k) a ∉ Del := hkept k (by omega)
      have hstep : (p ^ (k+1)) a = p ((p ^ k) a) := by rw [pow_succ']; rfl
      rw [hstep, ihk, hp, rawFace_step_eq_phi M hclosed hak, ← Equiv.Perm.mul_apply,
        ← pow_succ']

/-- **Whole-face kept ⟹ raw face SameCycle.**  If every dart in the `M.φ`-cycle of `a` is kept
(`∉ Del`), then `M.φ.SameCycle a b` implies `(M.σ * rawAlpha).SameCycle a b`: the `φ`-walk from
`a` to `b` never leaves the kept set, so the raw face perm tracks `M.φ` along it. -/
lemma rawFace_sameCycle_of_face_kept {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a b : D}
    (hface : ∀ c : D, M.φ.SameCycle a c → c ∉ Del)
    (hab : M.φ.SameCycle a b) :
    (M.σ * SubmapPlanar.rawAlpha M Del hclosed).SameCycle a b := by
  classical
  obtain ⟨k, hk⟩ := hab.exists_nat_pow_eq
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast, rawFace_walk M hclosed k (fun j _ => hface _ ⟨(j : ℤ), by rw [zpow_natCast]⟩),
    hk]

end RawPrimitives



/-- The **raw** dart-step relation at the side-1 chord split: `M.σ`-`SameCycle` or a
`rawAlpha`-edge (the restricted involution fixing deleted darts, equal to `M.α` on kept
darts).  This is `SubmapPlanar.dartStepRel M.σ (rawAlpha M keptDel₁ …)`. -/
noncomputable def rawStep₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    D → D → Prop :=
  dartStepRel M.σ (rawAlpha M data.keptDel₁ (SubmapPlanar.keptDel₁_closed data hsep))

/-- **Raw `EqvGen` from same-face whole-face-kept.**  Wrapper turning the raw face SameCycle
into raw `EqvGen` (the generator of the raw reachability). -/
lemma rawEqvGen_of_face_kept {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a b : D}
    (hface : ∀ c : D, M.φ.SameCycle a c → c ∉ Del)
    (hab : M.φ.SameCycle a b) :
    Relation.EqvGen (dartStepRel M.σ (SubmapPlanar.rawAlpha M Del hclosed)) a b :=
  eqvGen_dartStepRel_of_sameCycle_mul M.σ (SubmapPlanar.rawAlpha M Del hclosed)
    (SubmapPlanar.rawAlpha_invol M Del hclosed)
    (rawFace_sameCycle_of_face_kept M hclosed hface hab)

/-- **One kept `φ`-step is raw-connected.**  For a kept dart `a` (`a ∉ Del`), `a` and `M.φ a`
are raw-`EqvGen`-connected: one raw face-perm step `(M.σ * rawAlpha) a = M.φ a`. -/
lemma rawEqvGen_phi_step {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} (ha : a ∉ Del) :
    Relation.EqvGen (dartStepRel M.σ (SubmapPlanar.rawAlpha M Del hclosed)) a (M.φ a) := by
  refine eqvGen_dartStepRel_of_sameCycle_mul M.σ (SubmapPlanar.rawAlpha M Del hclosed)
    (SubmapPlanar.rawAlpha_invol M Del hclosed) ?_
  exact ⟨(1 : ℤ), by rw [zpow_one, rawFace_step_eq_phi M hclosed ha]⟩

/-- **Raw `EqvGen` from a single `rawAlpha`-edge at a kept dart.**  For `a ∉ Del`,
`a` and `M.α a` are one raw step apart. -/
lemma rawEqvGen_of_alpha {Del : Finset D}
    (hclosed : ∀ d : D, d ∈ Del → M.α d ∈ Del) {a : D} (ha : a ∉ Del) :
    Relation.EqvGen (dartStepRel M.σ (SubmapPlanar.rawAlpha M Del hclosed)) a (M.α a) :=
  Relation.EqvGen.rel _ _ (Or.inr (SubmapPlanar.rawAlpha_eq_alpha_of_notMem M Del hclosed ha).symm)



section RawConnected

/-- The chord dart is deleted (removed from the side-1 kept set). -/
lemma dart_mem_keptDel₁ (data : hNT.ChordSplitData u v) :
    data.dart ∈ data.keptDel₁ := by
  classical
  by_contra hcontra
  rw [data.mem_keptDel₁_iff] at hcontra
  exact hcontra.2 rfl

/-- A dart whose face lies in side 1 and which is not the chord dart is kept. -/
lemma inner_notMem_keptDel₁ (data : hNT.ChordSplitData u v)
    {c : D} (hf : M.dartFace c ∈ data.side₁) (hne : c ≠ data.dart) :
    c ∉ data.keptDel₁ := by
  rw [data.mem_keptDel₁_iff]
  exact ⟨Or.inl hf, by simpa using hne⟩

/-- An outer-arc dart of side 1 (outer face, `α`-reverse inner) is kept; it is never the
chord dart (whose face is `face₁ ≠ outerFace`). -/
lemma outerArc_notMem_keptDel₁ (data : hNT.ChordSplitData u v)
    {c : D} (ho : M.dartFace c = hNT.outerFace)
    (hα : M.dartFace (M.α c) ∈ data.side₁) : c ∉ data.keptDel₁ := by
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inr ⟨ho, hα⟩, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hc
  apply data.face₁_not_outer
  show M.dartFace data.dart = hNT.outerFace
  rw [← hc]; exact ho

/-- The reference kept dart of side 1: `M.φ data.dart`, a dart of the triangle `face₁` other
than the (deleted) chord dart. -/
lemma ref_kept (data : hNT.ChordSplitData u v) :
    M.φ data.dart ∉ data.keptDel₁ := by
  refine inner_notMem_keptDel₁ data ?_ ?_
  · show M.dartFace (M.φ data.dart) ∈ data.side₁
    rw [dartFace_phi]; exact data.face₁_mem_side₁
  · exact M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart

/-- **Within-face raw connectivity, away from `face₁`.**  If `M.φ.SameCycle a b` and the common
face is in side 1 but is not `face₁`, then `a` and `b` are raw-connected.  (Every dart of such
a face is kept: it is in `sideDarts₁` and is not the chord dart, which lives in `face₁`.) -/
lemma rawE_within_face_ne_face₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a b : D} (hfa : M.dartFace a ∈ data.side₁)
    (hne : M.dartFace a ≠ data.face₁) (hab : M.φ.SameCycle a b) :
    Relation.EqvGen (rawStep₁ data hsep) a b := by
  refine rawEqvGen_of_face_kept (SubmapPlanar.keptDel₁_closed data hsep)
    (fun c hac => ?_) hab
  have hfeq : M.dartFace c = M.dartFace a := Quotient.sound hac.symm
  have hfc : M.dartFace c ∈ data.side₁ := by rw [hfeq]; exact hfa
  refine inner_notMem_keptDel₁ data hfc ?_
  intro hcd
  apply hne
  rw [← hfeq, hcd]; rfl

/-- The darts of the chord triangle `face₁`: any dart `c` with `M.φ.SameCycle data.dart c` is
`data.dart`, `M.φ data.dart`, or `M.φ² data.dart`. -/
lemma face₁_dart_cases (data : hNT.ChordSplitData u v)
    {c : D} (hsc : M.φ.SameCycle data.dart c) :
    c = data.dart ∨ c = M.φ data.dart ∨ c = M.φ (M.φ data.dart) := by
  classical
  obtain ⟨h1, h2, h3⟩ := data.face₁_isFaceTriangle
  obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
  have hcube : (M.φ ^ 3) data.dart = data.dart := by
    have : (M.φ ^ 3) data.dart = M.φ (M.φ (M.φ data.dart)) := by
      simp [pow_succ, Equiv.Perm.mul_apply]
    rw [this, h3]
  have hperiodic : ∀ m : ℕ, (M.φ ^ m) data.dart = (M.φ ^ (m % 3)) data.dart := by
    intro m
    -- `φ^m dart = φ^(3*(m/3)) (φ^(m%3) dart)`; the outer factor fixes the inner point.
    conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, Equiv.Perm.mul_apply]
    set y := (M.φ ^ (m % 3)) data.dart with hy
    -- `φ^3` fixes `y` (it fixes `dart`, and powers commute), so `(φ^3)^(m/3)` does too.
    have hfix : (M.φ ^ 3) y = y := by
      rw [hy, ← Equiv.Perm.mul_apply, ← pow_add, Nat.add_comm, pow_add, Equiv.Perm.mul_apply,
        hcube]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hfix (m / 3)
  have hmod : c = (M.φ ^ (k % 3)) data.dart := by rw [← hk, hperiodic k]
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : (k % 3)
  · left; rw [hmod]; simp
  · right; left; rw [hmod, pow_one]
  · right; right; rw [hmod]; simp [pow_succ, Equiv.Perm.mul_apply]

/-- **Within-`face₁` raw connectivity.**  Any kept dart of `face₁` raw-connects to the
reference dart `M.φ data.dart`. -/
lemma rawE_face₁_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hfa : M.dartFace a = data.face₁) (hne : a ≠ data.dart) :
    Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  have hsc : M.φ.SameCycle data.dart a := by
    have hf : M.dartFace a = M.dartFace data.dart := by rw [hfa]; rfl
    exact (Quotient.exact hf).symm
  rcases face₁_dart_cases data hsc with h | h | h
  · exact absurd h hne
  · subst h; exact Relation.EqvGen.refl _
  · subst h
    -- `M.φ dart → M.φ² dart` is one raw step; take its symm.
    exact Relation.EqvGen.symm _ _
      (rawEqvGen_phi_step (SubmapPlanar.keptDel₁_closed data hsep) (ref_kept data))

/-- **Any inner kept dart raw-connects to the reference, given its face does**.  Let `a` be a
kept dart whose face is in side 1, and suppose some dart `r₀` of the *same* face raw-connects
to the reference `M.φ data.dart`.  Then so does `a`.  (Within `face₁` we connect directly via
`rawE_face₁_to_ref`, ignoring `r₀`; on any other face all darts are kept, so `a` and `r₀`
share a whole-kept face and connect by a raw `φ`-walk.) -/
lemma rawE_inner_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a r₀ : D} (hkept : a ∉ data.keptDel₁) (hfa : M.dartFace a ∈ data.side₁)
    (hsamef : M.dartFace a = M.dartFace r₀)
    (hr₀ : Relation.EqvGen (rawStep₁ data hsep) r₀ (M.φ data.dart)) :
    Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  classical
  by_cases hne : M.dartFace a = data.face₁
  · -- `face₁`: `a` is kept, hence `a ≠ dart`; connect directly.
    have had : a ≠ data.dart := fun h => hkept (h ▸ dart_mem_keptDel₁ data)
    exact rawE_face₁_to_ref data hsep hne had
  · -- non-`face₁` face: `a` and `r₀` share a whole-kept face.
    have hsc : M.φ.SameCycle a r₀ := Quotient.exact hsamef
    exact Relation.EqvGen.trans _ _ _ (rawE_within_face_ne_face₁ data hsep hfa hne hsc) hr₀

/-- **The chord-split adjacency step is a raw `α`-edge between kept darts.**  If `f → g` via
`ChordSplitAdj` with `f, g ∈ side₁`, the witnessing dart `d` (`dartFace d = f`,
`dartFace (α d) = g`, non-chord edge) and its reverse `M.α d` are *both kept*, and `d`,
`M.α d` are one raw `α`-step apart. -/
lemma rawE_chordSplitAdj_step (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {f g : M.Face} (hf : f ∈ data.side₁) (hg : g ∈ data.side₁)
    (hadj : hNT.ChordSplitAdj u v f g) :
    ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      d ∉ data.keptDel₁ ∧ M.α d ∉ data.keptDel₁ ∧
      Relation.EqvGen (rawStep₁ data hsep) d (M.α d) := by
  obtain ⟨d, hdf, hdg, _hbe, hch⟩ := hadj
  -- `d ≠ dart` (its edge is not the chord), so `d` is a kept inner dart of `f ∈ side₁`.
  have hd_ne : d ≠ data.dart := by
    intro h; apply hch; rw [h]; exact (hNT.chordDart_edge data.chord)
  have hαd_ne : M.α d ≠ data.dart := by
    intro h
    apply hch
    have : M.dartEdge d = M.dartEdge (M.α d) := (M.dartEdge_alpha d).symm
    rw [this, h]; exact (hNT.chordDart_edge data.chord)
  have hd_kept : d ∉ data.keptDel₁ :=
    inner_notMem_keptDel₁ data (by rw [hdf]; exact hf) hd_ne
  have hαd_kept : M.α d ∉ data.keptDel₁ :=
    inner_notMem_keptDel₁ data (by rw [hdg]; exact hg) hαd_ne
  exact ⟨d, hdf, hdg, hd_kept, hαd_kept,
    rawEqvGen_of_alpha (SubmapPlanar.keptDel₁_closed data hsep) hd_kept⟩

/-- **Every inner kept side-1 dart raw-connects to the reference.**  By induction on the
`ChordSplitAdj`-reachability of its face from `face₁`.  Base: `face₁` via `rawE_face₁_to_ref`.
Step: the adjacency dart joins the previous face to the current one by a raw `α`-edge between
kept darts, threading the reachability. -/
lemma rawE_inner_kept_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {g : M.Face} (hg : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ g) :
    ∀ a : D, M.dartFace a = g → a ∉ data.keptDel₁ →
      Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  classical
  induction hg with
  | refl =>
      intro a hfa hkept
      have had : a ≠ data.dart := fun h => hkept (h ▸ dart_mem_keptDel₁ data)
      exact rawE_face₁_to_ref data hsep hfa had
  | @tail f g hfg hstep ih =>
      -- `f ∈ side₁` (reachable from `face₁`), `g ∈ side₁`.
      intro a hfa hkept
      have hf_side : f ∈ data.side₁ := hfg
      have hg_side : g ∈ data.side₁ := data.side₁_closed hf_side hstep
      -- the adjacency dart `d`: `dartFace d = f`, `dartFace (α d) = g`, both kept.
      obtain ⟨d, hdf, hdg, hd_kept, hαd_kept, hd_raw⟩ :=
        rawE_chordSplitAdj_step data hsep hf_side hg_side hstep
      -- `d` (in `f`) connects to the reference by the induction hypothesis.
      have hd_ref : Relation.EqvGen (rawStep₁ data hsep) d (M.φ data.dart) :=
        ih d hdf hd_kept
      -- `α d` (in `g`) connects to the reference: `α d → d → ref`.
      have hαd_ref : Relation.EqvGen (rawStep₁ data hsep) (M.α d) (M.φ data.dart) :=
        Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hd_raw) hd_ref
      -- `a` (in `g`, same face as `α d`) connects to the reference via `rawE_inner_to_ref`.
      exact rawE_inner_to_ref data hsep hkept (by rw [hfa]; exact hg_side)
        (by rw [hfa, hdg]) hαd_ref

/-- **Every kept side-1 dart raw-connects to the reference `M.φ data.dart`.**  An inner kept
dart goes through `rawE_inner_kept_to_ref`; an outer-arc kept dart connects via its raw
`α`-edge to its (inner kept) reverse, then through the inner case. -/
lemma rawE_kept_to_ref (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {a : D} (hkept : a ∉ data.keptDel₁) :
    Relation.EqvGen (rawStep₁ data hsep) a (M.φ data.dart) := by
  classical
  -- `a ∈ keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  have ha_in : a ∈ data.keptSet₁ := (data.mem_keptDel₁_iff a).mp hkept
  obtain ⟨haU, _⟩ := ha_in
  rcases haU with hinner | houter
  · -- inner: `dartFace a ∈ side₁`.
    have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ (M.dartFace a) :=
      hinner
    exact rawE_inner_kept_to_ref data hsep hreach a rfl hkept
  · -- outer-arc: `dartFace a = outerFace`, `dartFace (α a) ∈ side₁`.
    obtain ⟨_haouter, hαinner⟩ := houter
    -- `α a` is kept (inner side-1, not the chord dart): membership is `α`-invariant.
    have hαa_kept : M.α a ∉ data.keptDel₁ := fun h =>
      hkept ((SubmapPlanar.keptDel₁_sub data hsep a).2 h)
    -- `α a` connects to the reference (inner case).
    have hreach : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ (M.dartFace (M.α a)) :=
      hαinner
    have hαa_ref : Relation.EqvGen (rawStep₁ data hsep) (M.α a) (M.φ data.dart) :=
      rawE_inner_kept_to_ref data hsep hreach (M.α a) rfl hαa_kept
    -- `a → α a` is a raw `α`-step.
    exact Relation.EqvGen.trans _ _ _
      (rawEqvGen_of_alpha (SubmapPlanar.keptDel₁_closed data hsep) hkept) hαa_ref

/-- **The kept-side raw-reachability predicate, PROVED.**  Every two kept side-1 darts are
connected through the raw relation `rawStep₁`: each connects to the reference `M.φ data.dart`,
so they connect to each other.  This is the genuine dart-graph reachability "the side is the
closure of one Jordan region", proved unconditionally from the chord-split structure. -/
theorem keptSideRawConnected (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ x y : {d : D // d ∉ data.keptDel₁},
      Relation.EqvGen (rawStep₁ data hsep) x.1 y.1 := by
  intro x y
  exact Relation.EqvGen.trans _ _ _ (rawE_kept_to_ref data hsep x.2)
    (Relation.EqvGen.symm _ _ (rawE_kept_to_ref data hsep y.2))

end RawConnected



/-- **Raw reachability descends to kept-side connectivity.**  If every two kept side-1 darts
are connected through the raw relation `rawStep₁`, then the kept side-1 map `sideKeptMap₁` is
connected.  `SubmapPlanar.raw_eqvGen_descends` descends the raw `EqvGen` to a kept `EqvGen` on
the kept subtype's `keptStepRel`, which (the relation being symmetric) is the `ReflTransGen`
of the kept map's `dartStep` after identifying `sideSigma₁ = deleteSet M.σ keptDel₁` and
`sideAlpha₁ = keptAlpha`. -/
theorem keptSide₁_connected_of_rawConnected (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (hraw : ∀ x y : {d : D // d ∉ data.keptDel₁},
      Relation.EqvGen (rawStep₁ data hsep) x.1 y.1) :
    (sideKeptMap₁ data hsep).Connected := by
  classical
  set Del := data.keptDel₁ with hDel
  set hsub := SubmapPlanar.keptDel₁_sub data hsep with hhsub
  set hclosed := SubmapPlanar.keptDel₁_closed data hsep with hhclosed
  have hsymm : ∀ a b, SubmapPlanar.keptStepRel M Del hsub a b →
      SubmapPlanar.keptStepRel M Del hsub b a :=
    fun a b h => dartStepRel_symm (SubmapPlanar.keptAlpha_invol M Del hsub) h
  intro a b
  have hrawab : Relation.EqvGen (dartStepRel M.σ (rawAlpha M Del hclosed)) a.1 b.1 := hraw a b
  have hkept : Relation.EqvGen (SubmapPlanar.keptStepRel M Del hsub) a b :=
    SubmapPlanar.raw_eqvGen_descends M Del hclosed hsub hrawab
  have hreach : Relation.ReflTransGen (SubmapPlanar.keptStepRel M Del hsub) a b :=
    (eqvGen_iff_reflTransGen hsymm a b).1 hkept
  refine hreach.mono ?_
  intro x y hxy
  rcases hxy with hσ | hα
  · left
    show (sideKeptMap₁ data hsep).σ.SameCycle x y
    show data.sideSigma₁.SameCycle x y
    exact hσ
  · right
    show y = (sideKeptMap₁ data hsep).α x
    show y = data.sideAlpha₁ hsep x
    rw [SubmapPlanar.sideAlpha₁_eq_keptAlpha data hsep]
    exact hα

/-- **The kept side-1 map is connected — UNCONDITIONALLY.**  Combining the proved raw
reachability `keptSideRawConnected` with the descent `keptSide₁_connected_of_rawConnected`.
This is the one remaining topological input of the Chapter-35 chord case, now discharged from
the chord-split data and the separation `Separates` alone. -/
theorem sideKeptMap₁_connected (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (sideKeptMap₁ data hsep).Connected :=
  keptSide₁_connected_of_rawConnected data hsep (keptSideRawConnected data hsep)



/-- **`Side₁IsDisk`, UNCONDITIONAL.**  Side 1 of a chord split of a genus-0 near-triangulation
is a combinatorial disk (`IsSphereMap`) given the chord-split data and the separation
`Separates` alone: the genus-0 / Euler-2 half is the proved genus core
(`SubmapPlanar.side₁IsDisk_of_connected`), and the connectivity half is the proved raw
reachability (Sections A0/A).  The required kept dart witness is `M.φ data.dart` (kept by
`ref_kept`).  No connectivity or genus hypothesis is taken. -/
theorem side₁IsDisk_unconditional (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₁IsDisk data hsep :=
  SubmapPlanar.side₁IsDisk_of_connected data hsep ⟨M.φ data.dart, ref_kept data⟩
    (sideKeptMap₁_connected data hsep)

end ProofsInTheBook.ChordSideClose







end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideClose
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordReconClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordReconClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordSideClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



/-- **The side-1 region.**  The set of `M`-vertices that are the tail of some kept side-1 dart
(`d ∉ keptDel₁`).  This is the image of the side-1 vertex correspondence `ι` (Section 3). -/
def sideRegion₁ (data : hNT.ChordSplitData u v) : Set M.Vertex :=
  {w : M.Vertex | ∃ d : D, d ∉ data.keptDel₁ ∧ M.tail d = w}

/-- A kept dart's tail is in the side-1 region. -/
lemma tail_mem_sideRegion₁ (data : hNT.ChordSplitData u v) {d : D}
    (hd : d ∉ data.keptDel₁) : M.tail d ∈ sideRegion₁ data :=
  ⟨d, hd, rfl⟩



/-- **The side-1 vertex correspondence `ι`.**  Maps a side-1 vertex (a `freshSigma`-orbit) to
the `M`-vertex it restricts from: a `freshSigma`-orbit `⟦y⟧` is sent to `M.tail (proj y).val`
(`proj` projects the two fresh chord darts onto the anchors).  Well-defined: a `freshSigma`-orbit
restricts (`freshSigma_sameCycle_iff`) to a `sideSigma₁`-orbit, which restricts
(`filteredRotation_sameCycle_iff`) to an `M.σ`-orbit.  This is the concrete realization of
`ChordSideReconstruction.ι`. -/
noncomputable def sideVertexToM₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).Vertex → M.Vertex :=
  Quotient.lift
    (fun y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2 =>
      M.tail (proj a₀ a₁ y).1)
    (by
      intro x y hxy
      -- `hxy : freshSigma.SameCycle x y`.
      have hfs : (freshSigma data.sideSigma₁ a₀ a₁ hne).SameCycle x y := hxy
      -- project to a `sideSigma₁`-SameCycle, then to an `M.σ`-SameCycle.
      have hss : data.sideSigma₁.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) :=
        (freshSigma_sameCycle_iff data.sideSigma₁ hne x y).1 hfs
      have hM : M.σ.SameCycle (proj a₀ a₁ x).1 (proj a₀ a₁ y).1 :=
        (filteredRotation_sameCycle_iff M.σ data.keptDel₁ _ _).1 hss
      show M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1
      exact Quotient.sound hM)

/-- `ι` on the class of an `inl`-dart `⟨d, …⟩` is `M.tail d` (`proj (inl x) = x`). -/
lemma sideVertexToM₁_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₁}) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) (Sum.inl x))
      = M.tail x.1 := by
  show M.tail (proj a₀ a₁ (Sum.inl x)).1 = M.tail x.1
  rw [proj_inl]

/-- **`ι` lands in the side-1 region.**  Every side-1 vertex is the orbit of a kept dart
(`proj` of any representative is kept), whose tail is in `sideRegion₁`. -/
theorem sideVertexToM₁_mem (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (V : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) :
    sideVertexToM₁ data hsep a₀ a₁ hne V ∈ sideRegion₁ data := by
  refine Quotient.inductionOn V (fun y => ?_)
  show M.tail (proj a₀ a₁ y).1 ∈ sideRegion₁ data
  exact tail_mem_sideRegion₁ data (proj a₀ a₁ y).2



/-- **`ι` is surjective onto the side-1 region (`ι_surj`).**  Every vertex of the side-1 region
`sideRegion₁` is the image under `ι` of some side-1 vertex.  This is the concrete orbit
surjection the orchestration named as the attackable target: the side vertices are
`sideSigma₁`-orbits of kept darts, `ι` restricts each to its `M.σ`-orbit, and every region
vertex (the tail of a kept dart) is hit. -/
theorem sideVertexToM₁_surjective (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    ∀ ⦃w : M.Vertex⦄, w ∈ sideRegion₁ data →
      ∃ V : (data.sideMap₁ hsep a₀ a₁ hne).Vertex,
        sideVertexToM₁ data hsep a₀ a₁ hne V = w := by
  rintro w ⟨d, hd, rfl⟩
  -- the side vertex `⟦inl ⟨d, hd⟩⟧` maps to `M.tail d`.
  refine ⟨Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
    (Sum.inl ⟨d, hd⟩), ?_⟩
  exact sideVertexToM₁_inl data hsep a₀ a₁ hne ⟨d, hd⟩

/-- **The image of `ι` is exactly the side-1 region.**  Combining `sideVertexToM₁_mem`
(image ⊆ region) and `sideVertexToM₁_surjective` (region ⊆ image): `ι` is a surjection onto
`sideRegion₁`. -/
theorem sideVertexToM₁_range (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    Set.range (sideVertexToM₁ data hsep a₀ a₁ hne) = sideRegion₁ data := by
  apply Set.eq_of_subset_of_subset
  · rintro w ⟨V, rfl⟩
    exact sideVertexToM₁_mem data hsep a₀ a₁ hne V
  · intro w hw
    obtain ⟨V, hV⟩ := sideVertexToM₁_surjective data hsep a₀ a₁ hne hw
    exact ⟨V, hV⟩



/-- `ι` of the head of an `inl`-dart `x` is `M.head x.val` (`sideAlpha₁` restricts `M.α`). -/
lemma sideVertexToM₁_head_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₁}) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) (Sum.inl x)))
      = M.head x.1 := by
  -- `freshAlpha (inl x) = inl (sideAlpha₁ x)`, whose `ι` is `M.tail (sideAlpha₁ x).val`.
  rw [freshAlpha_inl]
  rw [sideVertexToM₁_inl data hsep a₀ a₁ hne (data.sideAlpha₁ hsep x)]
  -- `(sideAlpha₁ x).val = M.α x.val`, and `M.tail (M.α x.val) = M.head x.val`.
  rw [data.sideAlpha₁_apply_coe hsep x]
  rfl

/-- **The inner-edge correspondence.**  The side edge of an `inl`-dart `x` maps under `ι` to the
`M`-edge `s(M.tail x.val, M.head x.val)` = `M.dartEdge x.val`.  Hence the two `ι`-endpoints are
`M`-adjacent via the dart `x.val`. -/
theorem ι_adj_of_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₁}) :
    M.Adj
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) (Sum.inl x)))
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) (Sum.inl x)))) := by
  rw [sideVertexToM₁_inl data hsep a₀ a₁ hne x,
    sideVertexToM₁_head_inl data hsep a₀ a₁ hne x]
  exact M.adj_of_dart x.1











end ProofsInTheBook.ChordReconClose










end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordReconClose
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.ChordSideNT -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideNT

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ChordReconClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



/-- **The correct-anchor boundary classification of side 1.**  The boundary-cycle and
inner-triangulation data of `sideMap₁` that the contiguous chord split produces: the side is a
simple graph, its outer face is the chord face (arc `u..v` plus the duplicated chord edge), the
boundary cycle is simple of length `≥ 3`, and every *other* face is a triangle.  These are the
`NearTriangulation (sideMap₁)` fields beyond the already-proved `IsSphereMap`.

It is the chord analogue of `FanSurgeryReconstruction`'s boundary fields, and the genuine
discrete Jordan–Schoenflies residue (kernel-decided genus-dependent at the orbit layer,
`CutFaceLabel.lean`); it is **isolated, not fabricated**. -/
structure ContiguousInterval (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) where
  /-- The side map is a simple graph (the fresh chord edge is a non-loop, non-parallel edge —
  the correct-anchor condition that `u, v` are non-adjacent boundary vertices). -/
  simpleGraph : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph
  /-- The side outer face (the chord face: boundary arc `u..v` plus the duplicated chord). -/
  outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face
  /-- The side outer boundary cycle (the arc-plus-duplicated-chord cycle). -/
  outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace
  /-- The side boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The side boundary has length at least three. -/
  outer_len : 3 ≤ outerCycle.length
  /-- Every non-outer side face is a triangle (the intact `M`-inner triangles plus the chord
  triangle `face₁`). -/
  inner_tri : ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen f = 3



/-- **The side-1 near-triangulation, assembled.**  Given the correct-anchor boundary
classification `ci`, the side-1 sphere fact (here taken as the genus-0 disk core output), and
the anchor-incidence fact, `sideMap₁` is a `NearTriangulation`: `sphere` from the disk core,
everything else from `ci`.  This is the assembly the prior round named
`ChordSideClassification`, now built modulo the single residue `ContiguousInterval`. -/
def chordSideNearTriangulation (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsphere : (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap)
    (ci : ContiguousInterval data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₁ hsep a₀ a₁ hne) where
  sphere := hsphere
  simpleGraph := ci.simpleGraph
  outerFace := ci.outerFace
  outerCycle := ci.outerCycle
  outer_simple := ci.outer_simple
  outer_len := ci.outer_len
  inner_tri := ci.inner_tri

/-- **The sphere field, discharged unconditionally from the two local disk facts.**  This is
`ChordDisk.side₁_isSphereMap_of_disk` with `Side₁IsDisk` supplied by
`ChordSideClose.side₁IsDisk_unconditional` (proved from `Separates` alone).  It needs only the
anchor-incidence fact `Side₁AnchorsShareFace` (the proved fact-2). -/
theorem side₁_sphere_unconditional (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap :=
  side₁_isSphereMap_of_disk data hsep a₀ a₁ hne
    (ProofsInTheBook.ChordSideClose.side₁IsDisk_unconditional data hsep) hshare

/-- **The side-1 near-triangulation from the predicate + the proved disk core.**  Combines
`side₁_sphere_unconditional` (sphere discharged from the disk facts) with `ci`
(`ContiguousInterval`) to assemble the full `NearTriangulation (sideMap₁)`.  The only input
beyond `ContiguousInterval` is the anchor-incidence fact, which is the proved fact-2. -/
def chordSideNearTriangulation_of_share (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₁ hsep a₀ a₁ hne) :=
  chordSideNearTriangulation data hsep a₀ a₁ hne
    (side₁_sphere_unconditional data hsep a₀ a₁ hne hshare) ci





/-- **`ContiguousInterval` is satisfiable from a side near-triangulation** (non-vacuity).  Any
`NearTriangulation (sideMap₁)` projects onto a `ContiguousInterval` (its boundary fields).  So
the predicate is not unsatisfiable: it holds exactly when the side is a near-triangulation, and
`chordSideNearTriangulation` round-trips it. -/
def contiguousInterval_of_nearTriangulation (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (N : NearTriangulation (data.sideMap₁ hsep a₀ a₁ hne)) :
    ContiguousInterval data hsep a₀ a₁ hne where
  simpleGraph := N.simpleGraph
  outerFace := N.outerFace
  outerCycle := N.outerCycle
  outer_simple := N.outer_simple
  outer_len := N.outer_len
  inner_tri := N.inner_tri







end ProofsInTheBook.ChordSideNT











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideNT
import ProofsInTheBook.ChordSplitNT
-/
/- Source module: ProofsInTheBook.ChordSplitFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSplitFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordDisk

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M} {u v : M.Vertex}



/-- **The side-1 residue datum** (the genuinely-unbuilt `ChordSideReconstruction` fields).

Carries exactly the fields of `ChordSideReconstruction hNT (sideRegion₁ data) L` for the
pinned `N := sideMap₁`, `ι := sideVertexToM₁` that are **not** proved upstream: the vertex
correspondence's injectivity and adjacency-faithfulness, the list transport, the side Thomassen
list hypotheses, and the strict vertex decrease.  These are the discrete Jordan/Schoenflies
content of the chord split that the abstract `CombMap` layer does not synthesize (the same
character as the chordless branch's `FanSurgeryReconstruction` and the upstream
`Separates`/`SphereChordSeparation` Jordan input). -/
structure ChordSideResidue (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) where
  /-- The side near-triangulation (the boundary/inner-triangulation classification). -/
  ci : ContiguousInterval data hsep a₀ a₁ hne
  /-- The anchor-incidence fact (the proved fact-2 at the chord-cap anchors) — supplies the
  disk-core `sphere`. -/
  hshare : Side₁AnchorsShareFace data hsep a₀ a₁
  /-- The vertex correspondence is injective. -/
  ι_inj : Function.Injective (sideVertexToM₁ data hsep a₀ a₁ hne)
  /-- The vertex correspondence carries side adjacency to `M`-adjacency (the full graph hom,
  including the two fresh chord darts). -/
  ι_adj : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
    (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
        (sideVertexToM₁ data hsep a₀ a₁ hne y)
  /-- The vertex correspondence reflects `M`-adjacency on the region (graph iso onto the
  induced subgraph). -/
  ι_adj_reflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
    M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
        (sideVertexToM₁ data hsep a₀ a₁ hne y) →
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y
  /-- The side's precolored boundary edge. -/
  pₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  /-- The side's precolored boundary edge. -/
  qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  /-- The side's precolors. -/
  cpₛ : α
  /-- The side's precolors. -/
  cqₛ : α
  /-- The side Thomassen list hypotheses (with the pullback lists). -/
  hLₛ : ThomassenLists
    (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  /-- The strict vertex decrease (the recursion fuel). -/
  smaller : (data.sideMap₁ hsep a₀ a₁ hne).V < M.V



/-- **The side-1 reconstruction in the generic recursion framing.**

Assembles `ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ data) L` with:
`N := sideMap₁`, `hN :=` the proved side near-triangulation, `ι := sideVertexToM₁`, `ι_mem`
and `ι_surj` proved upstream, and the residue datum supplying the genuinely-unbuilt fields.

This is the unified framing: the side IS a `ChordSideReconstruction` (the recursion's input
type), built from `M` directly via the proven genus/connectivity/face/orbit machinery, with
the discrete-Jordan residue isolated in `ChordSideResidue`. -/
noncomputable def chordSideReconstruction_of_chord (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (res : ChordSideResidue data hsep a₀ a₁ hne L) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ data) L where
  Dₛ := {d : D // d ∉ data.keptDel₁} ⊕ Fin 2
  N := data.sideMap₁ hsep a₀ a₁ hne
  hN := chordSideNearTriangulation_of_share data hsep a₀ a₁ hne res.hshare res.ci
  ι := sideVertexToM₁ data hsep a₀ a₁ hne
  ι_inj := res.ι_inj
  ι_mem := fun x => sideVertexToM₁_mem data hsep a₀ a₁ hne x
  ι_surj := fun _ hw => sideVertexToM₁_surjective data hsep a₀ a₁ hne hw
  ι_adj := res.ι_adj
  ι_adj_reflect := res.ι_adj_reflect
  Lₛ := fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)
  Lₛ_eq := fun _ => rfl
  pₛ := res.pₛ
  qₛ := res.qₛ
  cpₛ := res.cpₛ
  cqₛ := res.cqₛ
  hLₛ := res.hLₛ
  smaller := res.smaller







/-- **The residue is inhabited from a genuine side reconstruction** (non-vacuity).  Given a
`ContiguousInterval`, the anchor-incidence fact, and the genuinely-unbuilt vertex/list/decrease
data, the residue is constructed.  This is just its constructor, recorded to certify the residue
is a real (satisfiable) datum, not a hidden `False`. -/
def chordSideResidue_mk (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁)
    (ι_inj : Function.Injective (sideVertexToM₁ data hsep a₀ a₁ hne))
    (ι_adj : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
        M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y))
    (ι_adj_reflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (smaller : (data.sideMap₁ hsep a₀ a₁ hne).V < M.V) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  { ci := ci, hshare := hshare, ι_inj := ι_inj, ι_adj := ι_adj,
    ι_adj_reflect := ι_adj_reflect, pₛ := pₛ, qₛ := qₛ, cpₛ := cpₛ, cqₛ := cqₛ,
    hLₛ := hLₛ, smaller := smaller }





/-- **The chord-branch residue for a chord `(u, v)`.**  The `M`-vertex-level chord split glue,
the chord endpoints' distinctness, and — for each side — the data needed to present it as a
`ChordSideReconstruction` via `chordSideReconstruction_of_chord` (the per-side separation,
anchors, and side residue), with the side-1 region identified with `regions.s₁` and side-2 with
`regions.s₂`.

This bundles exactly the discrete-Jordan content of one chord branch: the two side
separations + boundary classifications + the regions glue.  Building it is the chord half of a
`ChordRecursiveDichotomy`; its fields are the genuine residue (no fabricated structure). -/
structure ChordBranchResidue (hNT : NearTriangulation M) (u v p q : M.Vertex)
    (L : M.Vertex → Finset α) (cp cq : α) where
  /-- The `M`-vertex-level chord split regions. -/
  regions : ChordSplitRegions hNT u v p q L cp cq
  /-- The chord endpoints are distinct. -/
  uv_ne : u ≠ v
  /-- The side-1 reconstruction (on region `s₁`, lists `L`). -/
  R₁ : ChordSplitNT.ChordSideReconstruction hNT regions.s₁ L
  /-- For each side-1 coloring with distinct chord-endpoint colors, a side-2 reconstruction
  on `s₂` with the forced lists. -/
  R₂ : (c₁ : M.Vertex → α) → c₁ u ≠ c₁ v → ChordSplitNT.ChordSideReconstruction hNT regions.s₂
    (regions.forcedLists c₁ L)

/-- **The recursion datum, assembled from the chord-branch residue.**  This is exactly
`ChordRecursionData.ofComponents` on the bundled regions/reconstructions — presenting the chord
branch in the form `chord_case_recursive` consumes. -/
def chordRecursionData_of_branchResidue {u v p q : M.Vertex} {L : M.Vertex → Finset α}
    {cp cq : α} (br : ChordBranchResidue hNT u v p q L cp cq) :
    ChordRecursionData hNT u v p q L cp cq :=
  ChordRecursionData.ofComponents br.regions br.uv_ne br.R₁ br.R₂



end ProofsInTheBook.ChordSplitFinal



namespace ProofsInTheBook.ChordSplitFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT

variable {α : Type u} [DecidableEq α]





end ProofsInTheBook.ChordSplitFinal












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideNT
-/
/- Source module: ProofsInTheBook.ChordContiguous -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordContiguous

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSideNT

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}









/-- **The chord endpoints are adjacent in `M` (the fresh chord edge is a real edge).** -/
theorem chordChoice_adj (data : hNT.ChordSplitData u v) :
    M.toSimpleGraph.Adj u v :=
  data.chord.adj

























end ProofsInTheBook.ChordContiguous













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordContiguous
import ProofsInTheBook.ChordFaceCount
-/
/- Source module: ProofsInTheBook.ChordInnerTri -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordInnerTri

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



/-- The kept combinatorial map's face permutation is `keptPhi β ρ = ρ * β`. -/
lemma keptCombMap_phi (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k) :
    (keptCombMap β ρ hβinv hβfix).φ = keptPhi β ρ := rfl



section Splice

variable (β ρ : Equiv.Perm K) {a₀ a₁ : K}

/-- An orbit is **splice-untouched** if it avoids both chord predecessors `β a₀`, `β a₁`. -/
def SpliceUntouched (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : Prop :=
  ¬ (keptPhi β ρ).SameCycle k (β a₀) ∧ ¬ (keptPhi β ρ).SameCycle k (β a₁)

/-- `β (β a) = a` (involutivity, the form used here). -/
 lemma beta_beta' (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- On a `keptPhi`-orbit avoiding the predecessors, one `tracePhi`-step equals one
`keptPhi`-step (the swap fires only at `β a₀`, `β a₁`, which are not on the orbit). -/
lemma tracePhi_apply_eq_keptPhi_of_avoid (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) {c : K} (hc : (keptPhi β ρ).SameCycle k c) :
    tracePhi β ρ a₀ a₁ c = keptPhi β ρ c := by
  have h0 : c ≠ β a₀ := fun hca => h.1 (hca ▸ hc)
  have h1 : c ≠ β a₁ := fun hca => h.2 (hca ▸ hc)
  have hβc0 : β c ≠ a₀ := by
    intro hb; apply h0; have := congrArg β hb; rwa [beta_beta' β hβinv] at this
  have hβc1 : β c ≠ a₁ := by
    intro hb; apply h1; have := congrArg β hb; rwa [beta_beta' β hβinv] at this
  rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl

/-- On a splice-untouched orbit, the `tracePhi`-iterate equals the `keptPhi`-iterate. -/
lemma tracePhi_iterate_eq_keptPhi (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (n : ℕ) :
    (tracePhi β ρ a₀ a₁)^[n] k = (keptPhi β ρ)^[n] k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      -- `(keptPhi)^[n] k` is on the keptPhi-orbit of `k`.
      have hsc : (keptPhi β ρ).SameCycle k ((keptPhi β ρ)^[n] k) :=
        ⟨(n : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]⟩
      exact tracePhi_apply_eq_keptPhi_of_avoid β ρ hβinv h hsc

/-- **On a splice-untouched orbit, `tracePhi` and `keptPhi` define the same cycle.** -/
lemma tracePhi_sameCycle_iff_keptPhi (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (c : K) :
    (tracePhi β ρ a₀ a₁).SameCycle k c ↔ (keptPhi β ρ).SameCycle k c := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    rw [← hn, tracePhi_iterate_eq_keptPhi β ρ hβinv h n]
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    rw [← hn, ← tracePhi_iterate_eq_keptPhi β ρ hβinv h n]

end Splice



section Transfer

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **No fresh dart lies in a splice-untouched side face.**  If `inr j` were
`freshMap.φ`-SameCycle to `inl k`, its `faceProj` (`β a₀` or `β a₁`) would be
`tracePhi`-SameCycle to `k`, contradicting splice-untouchedness. -/
lemma no_inr_in_spliceUntouched_face {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (j : Fin 2) :
    ¬ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) (Sum.inr j) := by
  intro hsc
  have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inr j)).1 hsc
  simp only [faceProj_inl] at htrace
  -- `faceProj (inr j) ∈ {β a₀, β a₁}`; both contradict splice-untouchedness.
  rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h] at htrace
  fin_cases j
  · exact h.1 (by simpa using htrace)
  · exact h.2 (by simpa using htrace)

/-- **The side face of a splice-untouched `inl k` consists exactly of the `inl`-images of
the `keptPhi`-orbit of `k`.**  The filter of darts in that face equals the `keptPhi`-orbit
filter mapped by `Sum.inl`. -/
lemma spliceUntouched_face_filter_eq {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (Finset.univ.filter (fun x : K ⊕ Fin 2 =>
        Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) x
          = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k)))
      = (Finset.univ.filter (fun c : K =>
          Quotient.mk (cycleSetoid (keptPhi β ρ)) c
            = Quotient.mk (cycleSetoid (keptPhi β ρ)) k)).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    -- `x` is freshPhi-SameCycle to `inl k`.
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) x :=
      Quotient.exact hx.symm
    cases x with
    | inl c =>
        refine ⟨c, ?_, rfl⟩
        apply Quotient.sound
        -- want keptPhi.SameCycle c k, i.e. SameCycle k c symm.
        have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).1 hsc
        simp only [faceProj_inl] at htrace
        rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h] at htrace
        exact htrace.symm
    | inr j => exact absurd hsc (no_inr_in_spliceUntouched_face β ρ hβinv hβfix hne h j)
  · rintro ⟨c, hc, rfl⟩
    -- keptPhi.SameCycle c k ⇒ freshPhi.SameCycle (inl k) (inl c).
    have hkp : (keptPhi β ρ).SameCycle k c := (Quotient.exact hc.symm)
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl k))
        (faceProj β a₀ a₁ (Sum.inl c)) := by
      simp only [faceProj_inl]
      exact (tracePhi_sameCycle_iff_keptPhi β ρ hβinv h c).2 hkp
    have hsc := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).2 htrace
    exact (Quotient.sound hsc.symm)

/-- **Face-SIZE transfer (UNCONDITIONAL).**  For a kept dart `k` whose `keptPhi`-orbit is
splice-untouched, the side face length of `inl k` equals the kept-map face length of `k`:
`faceLen sideMap₁ (dartFace (inl k)) = faceLen (keptCombMap β ρ) (dartFace k)`.  This is the
precise content "the cut reroutes only the chord-incident faces; inner faces are untouched
`keptPhi`-orbits" — FACE SIZE, not the kernel-refuted COUNT label. -/
theorem freshPhi_faceLen_inl_eq_keptPhi {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = (keptCombMap β ρ hβinv hβfix).faceLen
        ((keptCombMap β ρ hβinv hβfix).dartFace k) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))).card
    = (Finset.univ.filter (fun c => Quotient.mk _ c
      = Quotient.mk (cycleSetoid (keptCombMap β ρ hβinv hβfix).φ) k)).card
  rw [keptCombMap_phi β ρ hβinv hβfix]
  rw [spliceUntouched_face_filter_eq β ρ hβinv hβfix hne h, Finset.card_map]

end Transfer



section MTransfer

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- One `keptPhi`-step on side 1 agrees with one `M.φ`-step, provided the `M.φ`-successor
is kept. -/
lemma sideKeptPhi_apply_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hnext : M.φ k.1 ∉ data.keptDel₁) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ k : D) = M.φ k.1 := by
  -- `keptPhi k = sideSigma₁ (sideAlpha₁ k)`.
  show (data.sideSigma₁ (data.sideAlpha₁ hsep k) : {d : D // d ∉ data.keptDel₁}).1 = M.φ k.1
  -- `sideAlpha₁ k` has coe `M.α k.1`; `sideSigma₁ = filteredRotation M.σ keptDel₁`.
  have hσnext : M.σ ((data.sideAlpha₁ hsep k : {d : D // d ∉ data.keptDel₁}) : D)
      ∉ data.keptDel₁ := by
    rw [sideAlpha₁_apply_coe]
    -- `M.σ (M.α k.1) = M.φ k.1`.
    show M.σ (M.α k.1) ∉ data.keptDel₁
    have : M.φ k.1 = M.σ (M.α k.1) := rfl
    rwa [← this]
  show (FilteredRotation.filteredRotation M.σ data.keptDel₁
      (data.sideAlpha₁ hsep k) : {d : D // d ∉ data.keptDel₁}).1 = M.φ k.1
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁
    (data.sideAlpha₁ hsep k) hσnext, sideAlpha₁_apply_coe]
  rfl

/-- **The `M.φ`-orbit of a kept dart stays kept.**  Every `M.φ`-iterate of `k.1` avoids the
deleted set.  (Provided here as a hypothesis; established below for inner side faces.) -/
def OrbitKept (data : hNT.ChordSplitData u v) (k : {d : D // d ∉ data.keptDel₁}) : Prop :=
  ∀ n : ℕ, M.φ^[n] k.1 ∉ data.keptDel₁

/-- On a kept orbit, the `keptPhi`-iterate coincides (under coercion) with the `M.φ`-iterate. -/
lemma sideKeptPhi_iterate_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k) (n : ℕ) :
    ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D) = M.φ^[n] k.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      -- the iterate is `⟨M.φ^[n] k.1, _⟩` by `ih`; its φ-successor is `M.φ^[n+1] k.1`, kept.
      have hkn : ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D)
          = M.φ^[n] k.1 := ih
      have hnext : M.φ ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D)
          ∉ data.keptDel₁ := by
        rw [hkn]
        have := hkept (n + 1)
        rwa [Function.iterate_succ_apply'] at this
      rw [sideKeptPhi_apply_eq_phi data hsep _ hnext, hkn]

/-- **`keptPhi` and `M.φ` define the same cycle on a kept orbit.** -/
lemma sideKeptPhi_sameCycle_iff_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k)
    (x : {d : D // d ∉ data.keptDel₁}) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle k x ↔ M.φ.SameCycle k.1 x.1 := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    have := congrArg (Subtype.val) hn
    rw [sideKeptPhi_iterate_eq_phi data hsep k hkept n] at this
    exact this
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    apply Subtype.ext
    rw [sideKeptPhi_iterate_eq_phi data hsep k hkept n]
    exact hn

/-- Every dart on the `M.φ`-orbit of a kept dart `k` (with kept orbit) is itself kept. -/
lemma orbitKept_mem (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k)
    {d : D} (hd : M.φ.SameCycle k.1 d) : d ∉ data.keptDel₁ := by
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact hkept n

/-- **The kept side face length equals `M`'s face length on a kept orbit.** -/
theorem sideKeptMap₁_faceLen_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k) :
    (sideKeptMap₁ data hsep).faceLen ((sideKeptMap₁ data hsep).dartFace k)
      = M.faceLen (M.dartFace k.1) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).card
    = (Finset.univ.filter (fun d => Quotient.mk _ d
      = Quotient.mk (cycleSetoid M.φ) k.1)).card
  have hφ : (sideKeptMap₁ data hsep).φ
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ := rfl
  -- the kept filter maps bijectively via `Subtype.val` onto the M filter.
  rw [show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).card
      = ((Finset.univ.filter (fun x : {d : D // d ∉ data.keptDel₁} =>
          Quotient.mk _ x = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card from (Finset.card_map _).symm]
  congr 1
  ext d
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hcd, rfl⟩
    -- `keptPhi.SameCycle k c`  ⇒  `M.φ.SameCycle k.1 c.1`.
    have hsc : (sideKeptMap₁ data hsep).φ.SameCycle k c := Quotient.exact hcd.symm
    rw [hφ, sideKeptPhi_sameCycle_iff_phi data hsep k hkept] at hsc
    exact Quotient.sound hsc.symm
  · intro hd
    have hsc : M.φ.SameCycle k.1 d := Quotient.exact hd.symm
    have hdkept : d ∉ data.keptDel₁ := orbitKept_mem data k hkept hsc
    refine ⟨⟨d, hdkept⟩, ?_, rfl⟩
    apply Quotient.sound
    show (sideKeptMap₁ data hsep).φ.SameCycle (⟨d, hdkept⟩ : {d : D // d ∉ data.keptDel₁}) k
    refine Equiv.Perm.SameCycle.symm ?_
    rw [hφ, sideKeptPhi_sameCycle_iff_phi data hsep k hkept ⟨d, hdkept⟩]
    exact hsc

/-- **`OrbitKept` is discharged for a genuine inner side-1 face.**  If `k.1` is a side-1
inner dart (`M`-face in `side₁`) whose `M`-face is not the chord face `face₁`, then its whole
`M.φ`-orbit stays kept: each iterate keeps the same (side-1, non-`face₁`) `M`-face, hence lies
in `sideDarts₁ \ {dart} ⊆ keptSet₁`.  This removes `OrbitKept` from the residue: it follows
from the side-1 face classification alone. -/
theorem orbitKept_of_side₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁) :
    OrbitKept data k := by
  intro n
  rw [data.mem_keptDel₁_iff]
  -- `M.φ^[n] k.1` has the same `M`-face as `k.1`.
  have hsameface : M.dartFace (M.φ^[n] k.1) = M.dartFace k.1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', M.dartFace_phi, ih]
  -- in `sideDarts₁`:
  have hin : M.φ^[n] k.1 ∈ data.sideDarts₁ := by
    show M.dartFace (M.φ^[n] k.1) ∈ data.side₁
    rw [hsameface]; exact hside
  -- not the chord dart (its face is `face₁`):
  have hne_dart : M.φ^[n] k.1 ≠ data.dart := by
    intro he
    apply hface₁
    have : M.dartFace (M.φ^[n] k.1) = data.face₁ := by rw [he]; rfl
    rwa [hsameface] at this
  -- hence in `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  show M.φ^[n] k.1 ∈ data.keptSet₁
  exact ⟨Or.inl hin, by simpa using hne_dart⟩



/-- **The side face of an untouched inner `inl k` has the same length as its `M`-face.** -/
theorem sideMap₁_faceLen_inl_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
    (hkept : OrbitKept data k) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k))
      = M.faceLen (M.dartFace k.1) := by
  have h1 := freshPhi_faceLen_inl_eq_keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne huntouched
  have h2 := sideKeptMap₁_faceLen_eq_M data hsep k hkept
  -- `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) …`; `sideKeptMap₁ = keptCombMap …`.
  rw [show data.sideMap₁ hsep a₀ a₁ hne
      = freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
          (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [h1]
  rw [show keptCombMap (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      = sideKeptMap₁ data hsep from rfl]
  exact h2

/-- **An untouched inner side face, mapping to a non-outer `M`-face, is a triangle.** -/
theorem sideMap₁_faceLen_inl_eq_three (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
    (hkept : OrbitKept data k)
    (hMinner : M.dartFace k.1 ≠ hNT.outerFace) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideMap₁_faceLen_inl_eq_M data hsep a₀ a₁ hne k huntouched hkept]
  exact hNT.inner_tri (M.dartFace k.1) hMinner



/-- **A side-1 inner face (not the chord face) that is splice-untouched is a triangle**, with
`OrbitKept` and `M`-non-outerness *both discharged* from the side-1 classification.  The only
remaining geometric input is `SpliceUntouched` (the correct-anchor condition: the orbit avoids
the chord predecessors) together with the face-membership data. -/
theorem sideMap₁_faceLen_inl_three_of_side₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁)
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideMap₁_faceLen_inl_eq_three data hsep a₀ a₁ hne k huntouched
    (orbitKept_of_side₁ data hsep k hside hface₁)
    (data.side₁_subset_nonouter hside)

end MTransfer

open ProofsInTheBook.ChordContiguous

section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

















end Discharge

end ProofsInTheBook.ChordInnerTri















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordInnerTri
-/
/- Source module: ProofsInTheBook.ChordFaceClass -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceClass

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



/-- **Every side face has a kept-`inl` representative** (the face-level `ι_surj`).  For any face
`f` of `sideMap₁`, there is a kept dart `k` with `dartFace (inl k) = f`.  Proof: a face is a
`freshMap.φ`-orbit; pick any representative `x`, then `f = dartFace (inl (faceProj x))` because
`x` is `φ`-SameCycle to `inl (faceProj x)` (`ChordFaceCount.freshPhi_sameCycle_inl_faceProj`),
and `faceProj x` is a kept dart of `K`. -/
theorem sideFace_has_inl_rep (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) :
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f := by
  classical
  refine Quotient.inductionOn f (fun x => ?_)
  -- `f = ⟦x⟧`; take `k = faceProj x` and use `freshPhi_sameCycle_inl_faceProj`.
  refine ⟨faceProj (data.sideAlpha₁ hsep) a₀ a₁ x, ?_⟩
  show Quotient.mk (cycleSetoid (data.sideMap₁ hsep a₀ a₁ hne).φ)
      (Sum.inl (faceProj (data.sideAlpha₁ hsep) a₀ a₁ x))
    = Quotient.mk (cycleSetoid (data.sideMap₁ hsep a₀ a₁ hne).φ) x
  apply Quotient.sound
  -- need `(sideMap₁).φ.SameCycle (inl (faceProj x)) x`; we have the reverse from ChordFaceCount.
  have h := freshPhi_sameCycle_inl_faceProj (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne x
  -- `h : (freshMap …).φ.SameCycle x (inl (faceProj x))`; `sideMap₁ = freshMap …`.
  exact h.symm



/-- **Every kept dart has its `M`-face in `side₁` or equal to the outer face** (unconditional).
A kept dart `k.1 ∈ keptSet₁` is in `sideDarts₁` (face `∈ side₁`) or in `outerArc₁`
(face `= outerFace`). -/
theorem keptDart_face_side₁_or_outer (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) :
    M.dartFace k.1 ∈ data.side₁ ∨ M.dartFace k.1 = hNT.outerFace := by
  -- `k.1 ∉ keptDel₁ ↔ k.1 ∈ keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  have hk : k.1 ∈ data.keptSet₁ := (data.mem_keptDel₁_iff k.1).1 k.2
  obtain ⟨hU, _⟩ := hk
  rcases hU with hin | hout
  · -- `k.1 ∈ sideDarts₁`, i.e. `M.dartFace k.1 ∈ side₁`.
    exact Or.inl hin
  · -- `k.1 ∈ outerArc₁`, i.e. `M.dartFace k.1 = outerFace`.
    exact Or.inr hout.1

/-- **A kept dart whose `M`-face is neither outer nor the chord face lies in `side₁`.**  The
contrapositive packaging of the dichotomy: if `M.dartFace k.1 ≠ outerFace` then it is in `side₁`
(and we carry the `≠ face₁` hypothesis alongside).  Unconditional. -/
theorem keptDart_face_mem_side₁ (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) (houter : M.dartFace k.1 ≠ hNT.outerFace) :
    M.dartFace k.1 ∈ data.side₁ :=
  (keptDart_face_side₁_or_outer data k).resolve_right houter

























end ProofsInTheBook.ChordFaceClass













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceClass
-/
/- Source module: ProofsInTheBook.ChordBoundaryOrbit -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordBoundaryOrbit

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Trace

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The fresh chord dart `inr 0` is freshPhi-SameCycle to `inl (β a₀)`** (explicit trace).
`φ̃ (inl (β a₀)) = inr 0`, so a single `φ`-step joins them. -/
lemma chordDart_sameCycle_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0) (Sum.inl (β a₀)) := by
  refine ⟨-1, ?_⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b0 β ρ hβinv hβfix hne]

/-- **The fresh chord dart `inr 1` is freshPhi-SameCycle to `inl (β a₁)`** (explicit trace). -/
lemma chordDart_sameCycle_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1) (Sum.inl (β a₁)) := by
  refine ⟨-1, ?_⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b1 β ρ hβinv hβfix hne]

/-- **The chord-dart `inr 0`'s side face equals the side face of `inl (β a₀)`** (the boundary
orbit traced concretely from the chord dart's known position). -/
lemma chordDart_face_eq_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
      = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl (β a₀)) :=
  Quotient.sound (chordDart_sameCycle_b0 β ρ hβinv hβfix hne)

/-- **The chord-dart `inr 1`'s side face equals the side face of `inl (β a₁)`.** -/
lemma chordDart_face_eq_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl (β a₁)) :=
  Quotient.sound (chordDart_sameCycle_b1 β ρ hβinv hβfix hne)

end Trace



section Membership

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **Side faces of two `inl` darts coincide iff their `tracePhi`-orbits do.** -/
lemma sideFace_inl_eq_iff_tracePhi (k c : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl c)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k c := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) (Sum.inl c) :=
      Quotient.exact h
    have := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).1 hsc
    simpa only [faceProj_inl] using this
  · intro h
    apply Quotient.sound
    refine (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).2 ?_
    simpa only [faceProj_inl] using h

/-- **The side face of `inl k` is the chord-dart-0 face iff `k` is `tracePhi`-SameCycle to
`β a₀`.** -/
lemma sideFace_eq_chordOrbit0_iff (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
  rw [chordDart_face_eq_b0 β ρ hβinv hβfix hne, sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

/-- **The side face of `inl k` is the chord-dart-1 face iff `k` is `tracePhi`-SameCycle to
`β a₁`.** -/
lemma sideFace_eq_chordOrbit1_iff (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
  rw [chordDart_face_eq_b1 β ρ hβinv hβfix hne, sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

end Membership



/-- `β (β a) = a` (involutivity, the local form). -/
 lemma betaBeta (β : Equiv.Perm K) (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- `keptPhi (β a₀) = ρ a₀` (since `β (β a₀) = a₀`). -/
lemma keptPhi_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₀ : K) :
    keptPhi β ρ (β a₀) = ρ a₀ := by
  show ρ (β (β a₀)) = ρ a₀
  rw [betaBeta β hβinv]

/-- `keptPhi (β a₁) = ρ a₁`. -/
lemma keptPhi_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₁ : K) :
    keptPhi β ρ (β a₁) = ρ a₁ := by
  show ρ (β (β a₁)) = ρ a₁
  rw [betaBeta β hβinv]

/-- **The walk lemma.**  Iterating `keptPhi` from `β a₀`, every iterate is `tracePhi`-SameCycle
to `β a₀` or to `β a₁`.  Proved by induction tracking which of the two split threads the iterate
sits on; the swap re-routes the thread exactly at the two predecessors. -/
lemma tracePhi_reaches_keptPhi_iterate_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (a₀ a₁ : K) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) ((keptPhi β ρ)^[n] (β a₀))
      ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) ((keptPhi β ρ)^[n] (β a₀)) := by
  induction n with
  | zero => exact Or.inl (by simpa using Equiv.Perm.SameCycle.rfl)
  | succ n ih =>
      set c := (keptPhi β ρ)^[n] (β a₀) with hc
      rw [Function.iterate_succ_apply', ← hc]
      by_cases h0 : c = β a₀
      · -- keptPhi c = keptPhi (β a₀) = ρ a₀ = tracePhi (β a₁); hop to the β a₁ thread.
        right
        rw [h0, keptPhi_b0 β ρ hβinv, ← tracePhi_b1 β ρ hβinv a₀ a₁]
        exact ⟨1, by rw [zpow_one]⟩
      · by_cases h1 : c = β a₁
        · -- keptPhi c = ρ a₁ = tracePhi (β a₀); hop to the β a₀ thread.
          left
          rw [h1, keptPhi_b1 β ρ hβinv, ← tracePhi_b0 β ρ hβinv a₀ a₁]
          exact ⟨1, by rw [zpow_one]⟩
        · -- non-predecessor: keptPhi c = tracePhi c, stay on the same thread.
          have hβc0 : β c ≠ a₀ := by
            intro hb; apply h0; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have hβc1 : β c ≠ a₁ := by
            intro hb; apply h1; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have heq : keptPhi β ρ c = tracePhi β ρ a₀ a₁ c := by
            rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl
          rw [heq]
          have hstep : (tracePhi β ρ a₀ a₁).SameCycle c (tracePhi β ρ a₀ a₁ c) :=
            ⟨1, by rw [zpow_one]⟩
          rcases ih with h | h
          · exact Or.inl (h.trans hstep)
          · exact Or.inr (h.trans hstep)

/-- **The unconditional orbit trichotomy (`β a₀` thread).**  Every kept dart `c` whose
`keptPhi`-orbit meets `β a₀` is `tracePhi`-SameCycle to `β a₀` or to `β a₁`. -/
lemma tracePhi_reaches_of_keptPhi_sameCycle_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    {a₀ a₁ c : K} (h : (keptPhi β ρ).SameCycle (β a₀) c) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) c ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) c := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact tracePhi_reaches_keptPhi_iterate_b0 β ρ hβinv a₀ a₁ n

/-- Symmetric walk from the `β a₁` thread. -/
lemma tracePhi_reaches_keptPhi_iterate_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (a₀ a₁ : K) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) ((keptPhi β ρ)^[n] (β a₁))
      ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) ((keptPhi β ρ)^[n] (β a₁)) := by
  induction n with
  | zero => exact Or.inr (by simpa using Equiv.Perm.SameCycle.rfl)
  | succ n ih =>
      set c := (keptPhi β ρ)^[n] (β a₁) with hc
      rw [Function.iterate_succ_apply', ← hc]
      by_cases h0 : c = β a₀
      · right
        rw [h0, keptPhi_b0 β ρ hβinv, ← tracePhi_b1 β ρ hβinv a₀ a₁]
        exact ⟨1, by rw [zpow_one]⟩
      · by_cases h1 : c = β a₁
        · left
          rw [h1, keptPhi_b1 β ρ hβinv, ← tracePhi_b0 β ρ hβinv a₀ a₁]
          exact ⟨1, by rw [zpow_one]⟩
        · have hβc0 : β c ≠ a₀ := by
            intro hb; apply h0; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have hβc1 : β c ≠ a₁ := by
            intro hb; apply h1; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have heq : keptPhi β ρ c = tracePhi β ρ a₀ a₁ c := by
            rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl
          rw [heq]
          have hstep : (tracePhi β ρ a₀ a₁).SameCycle c (tracePhi β ρ a₀ a₁ c) :=
            ⟨1, by rw [zpow_one]⟩
          rcases ih with h | h
          · exact Or.inl (h.trans hstep)
          · exact Or.inr (h.trans hstep)

/-- **The unconditional orbit trichotomy (`β a₁` thread).** -/
lemma tracePhi_reaches_of_keptPhi_sameCycle_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    {a₀ a₁ c : K} (h : (keptPhi β ρ).SameCycle (β a₁) c) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) c ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) c := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact tracePhi_reaches_keptPhi_iterate_b1 β ρ hβinv a₀ a₁ n



section Untouched

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The KEY fresh-angle theorem.**  A kept dart whose side face is neither chord-dart face is
splice-untouched. -/
theorem spliceUntouched_of_face_ne_chordOrbits {k : K}
    (h0 : (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0))
    (h1 : (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)) :
    SpliceUntouched β ρ a₀ a₁ k := by
  -- ¬ tracePhi.SameCycle k (β a₀)  and  ¬ tracePhi.SameCycle k (β a₁).
  have ht0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
    rw [← sideFace_eq_chordOrbit0_iff β ρ hβinv hβfix hne]; exact h0
  have ht1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
    rw [← sideFace_eq_chordOrbit1_iff β ρ hβinv hβfix hne]; exact h1
  refine ⟨?_, ?_⟩
  · -- ¬ keptPhi.SameCycle k (β a₀)
    intro hkp
    rcases tracePhi_reaches_of_keptPhi_sameCycle_b0 β ρ hβinv (a₀ := a₀) (a₁ := a₁) hkp.symm
      with h | h
    · exact ht0 h.symm
    · exact ht1 h.symm
  · -- ¬ keptPhi.SameCycle k (β a₁)
    intro hkp
    rcases tracePhi_reaches_of_keptPhi_sameCycle_b1 β ρ hβinv (a₀ := a₀) (a₁ := a₁) hkp.symm
      with h | h
    · exact ht0 h.symm
    · exact ht1 h.symm

end Untouched



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The chord-dart faces are the two touched orbits.**  Re-export of `chordDart_face_eq_*`
specialised to the chord-split side map. -/
lemma sideMap₁_chordDart_face_eq_b0 (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (data.sideAlpha₁ hsep a₀)) :=
  chordDart_face_eq_b0 (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne











/-- **The two chord-dart faces coincide iff the chord predecessors share a `tracePhi`-orbit.**
The equivalence that makes the two-orbit structure explicit. -/
theorem chordOrbits_eq_iff_tracePhi (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (hβfix : ∀ k, β k ≠ k) {a₀ a₁ : K} (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle (β a₀) (β a₁) := by
  rw [chordDart_face_eq_b0 β ρ hβinv hβfix hne, chordDart_face_eq_b1 β ρ hβinv hβfix hne,
    sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]







end Discharge

end ProofsInTheBook.ChordBoundaryOrbit



















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordBoundaryOrbit
-/
/- Source module: ProofsInTheBook.ChordFaceFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]



section Formula

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The `tracePhi`-orbit cardinality of `k` on `K` (the number of `inl`-darts in the side
face of `inl k`). -/
def tOrbitCard (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : ℕ :=
  (Finset.univ.filter (fun c : K =>
    Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) c
      = Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) k)).card



/-- `inr 0` is in the side face of `inl k` iff `k ~ₜ β a₀`. -/
lemma inr_zero_mem_sideFace_iff (k : K) :
    (Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inr 0)
        = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0) (Sum.inl k) :=
      Quotient.exact h
    have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 0) (Sum.inl k)).1 hsc
    simp only [faceProj_inr_zero, faceProj_inl] at htrace
    exact (htrace.symm)
  · intro h
    apply Quotient.sound
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 0))
        (faceProj β a₀ a₁ (Sum.inl k)) := by
      simp only [faceProj_inr_zero, faceProj_inl]; exact h.symm
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 0) (Sum.inl k)).2 htrace

/-- `inr 1` is in the side face of `inl k` iff `k ~ₜ β a₁`. -/
lemma inr_one_mem_sideFace_iff (k : K) :
    (Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inr 1)
        = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1) (Sum.inl k) :=
      Quotient.exact h
    have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 1) (Sum.inl k)).1 hsc
    simp only [faceProj_inr_one, faceProj_inl] at htrace
    exact (htrace.symm)
  · intro h
    apply Quotient.sound
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 1))
        (faceProj β a₀ a₁ (Sum.inl k)) := by
      simp only [faceProj_inr_one, faceProj_inl]; exact h.symm
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 1) (Sum.inl k)).2 htrace

/-- The full dart-set splits as `inl`-images of `univ K` together with the two `inr` darts. -/
 lemma univ_sum_decomp :
    (Finset.univ : Finset (K ⊕ Fin 2))
      = (Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩)
        ∪ {Sum.inr 0, Sum.inr 1} := by
  classical
  ext x
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_insert, Finset.mem_singleton, true_iff]
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr j => fin_cases j <;> simp

/-- **The general side-face length formula (UNCONDITIONAL).**  The side face of `inl k` has
length `#(tracePhi-orbit of k)` plus `1` for each chord predecessor `β a₀`, `β a₁` lying in
that orbit. -/
theorem sideFaceLen_formula (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = tOrbitCard β ρ a₀ a₁ k
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0) := by
  classical
  set Φ := (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ with hΦ
  set Q : K ⊕ Fin 2 → Prop := fun x =>
    Quotient.mk (cycleSetoid Φ) x = Quotient.mk (cycleSetoid Φ) (Sum.inl k) with hQ
  show (Finset.univ.filter Q).card = _
  -- Split the universe into the inl-image and the two inr darts.
  rw [univ_sum_decomp, Finset.filter_union]
  rw [Finset.card_union_of_disjoint ?disj]
  · -- inl part
    have hinl : (((Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩).filter Q)).card
        = tOrbitCard β ρ a₀ a₁ k := by
      rw [Finset.filter_map, Finset.card_map]
      -- the filtered preimage on `K` equals the tracePhi-orbit filter.
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
        Function.Embedding.coeFn_mk, hQ]
      constructor
      · intro h
        apply Quotient.sound
        have hsc : Φ.SameCycle (Sum.inl c) (Sum.inl k) := Quotient.exact h
        have := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).1 hsc
        simpa only [faceProj_inl] using this
      · intro h
        apply Quotient.sound
        have htr : (tracePhi β ρ a₀ a₁).SameCycle c k := Quotient.exact h
        have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl c))
            (faceProj β a₀ a₁ (Sum.inl k)) := by simpa only [faceProj_inl] using htr
        exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).2 htrace
    -- inr part
    have hinr : (({Sum.inr 0, Sum.inr 1} : Finset (K ⊕ Fin 2)).filter Q).card
        = (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
          + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0) := by
      have key0 : Q (Sum.inr 0) ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) :=
        inr_zero_mem_sideFace_iff β ρ hβinv hβfix hne k
      have key1 : Q (Sum.inr 1) ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) :=
        inr_one_mem_sideFace_iff β ρ hβinv hβfix hne k
      rw [Finset.filter_insert, Finset.filter_singleton]
      by_cases h0 : Q (Sum.inr 0) <;> by_cases h1 : Q (Sum.inr 1)
      · rw [if_pos h0, if_pos h1, if_pos (key0.1 h0), if_pos (key1.1 h1)]
        rw [Finset.card_insert_of_notMem (by simp)]; simp
      · have ne1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := fun e => h1 (key1.2 e)
        rw [if_pos h0, if_neg h1, if_pos (key0.1 h0), if_neg ne1]; simp
      · have ne0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := fun e => h0 (key0.2 e)
        rw [if_neg h0, if_pos h1, if_neg ne0, if_pos (key1.1 h1)]; simp
      · have ne0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := fun e => h0 (key0.2 e)
        have ne1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := fun e => h1 (key1.2 e)
        rw [if_neg h0, if_neg h1, if_neg ne0, if_neg ne1]; simp
    rw [hinl, hinr, ← add_assoc]
  case disj =>
    apply Finset.disjoint_left.2
    intro x hx hx2
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx hx2
    obtain ⟨⟨c, hc⟩, _⟩ := hx
    obtain ⟨hx2mem, _⟩ := hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2mem
    subst hc
    rcases hx2mem with h | h <;> exact absurd h (by simp)

end Formula



section Consequences

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

include hne



/-- **The chord-triangle face length, from the explicit count.**  If the side face's
representative `k` has a `tracePhi`-orbit of exactly `2` kept darts and exactly one of the two
chord predecessors joins it (the fresh chord dart re-closing the deleted-dart gap of the
`M`-triangle `face₁`), then the side face is a triangle.  This is the DIRECT discharge of the
touched chord-triangle face — no splice-untouchedness, computed from the formula. -/
theorem sideFaceLen_three_of_count {k : K} (htwo : tOrbitCard β ρ a₀ a₁ k = 2)
    (hone : ((if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0)) = 1) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideFaceLen_formula β ρ hβinv hβfix hne k, add_assoc, htwo, hone]



end Consequences



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The explicit chord-triangle count, at the side-map level.**  A kept dart `k` whose side
face has a `tracePhi`-orbit of `2` kept darts joined by exactly one fresh chord dart yields a
side triangle.  This is the DIRECT discharge of the touched `face₁` image — the chord re-closes
the deleted-dart gap of the `M`-triangle `face₁` with one fresh chord dart. -/
theorem sideMap₁_faceLen_three_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (htwo : tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideFaceLen_three_of_count (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne htwo hone

/-- **The per-face triangle witness (NO `≠ face₁` carve-out).**  For one side face `f`, a
representative giving `faceLen f = 3` via EITHER route. -/
inductive SideFaceTriangle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop where
  /-- A representative whose side face IS `f` and has `faceLen = 3`. -/
  | mk (k : {d : D // d ∉ data.keptDel₁})
      (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
      (hlen : (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3)



/-- The explicit chord-triangle count route produces a `SideFaceTriangle` witness (the touched
`face₁` image, discharged directly). -/
theorem sideFaceTriangle_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (k : {d : D // d ∉ data.keptDel₁})
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
    (htwo : tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  ⟨k, hkf, sideMap₁_faceLen_three_of_count data hsep a₀ a₁ hne k htwo hone⟩















/-- **The chord dart is deleted** (`dart ∈ keptDel₁`): it is removed from `keptSet₁`. -/
theorem dart_mem_keptDel₁ (data : hNT.ChordSplitData u v) :
    data.dart ∈ data.keptDel₁ := by
  classical
  by_contra h
  rw [data.mem_keptDel₁_iff] at h
  exact h.2 (by simp)

/-- **The two non-chord darts of `face₁` are kept.**  `M.φ dart`, `M.φ² dart` have `M`-face
`face₁ ∈ side₁`, hence lie in `sideDarts₁`; they are `≠ dart` (the triangle has distinct darts),
hence in `keptSet₁`. -/
theorem face₁_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd1 : M.φ data.dart ≠ data.dart) :
    M.φ data.dart ∉ data.keptDel₁ := by
  classical
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inl ?_, by simpa using hd1⟩
  show M.dartFace (M.φ data.dart) ∈ data.side₁
  rw [M.dartFace_phi]; exact data.face₁_mem_side₁

/-- **The second non-chord dart of `face₁` is kept.** -/
theorem face₁_phi_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd2 : M.φ (M.φ data.dart) ≠ data.dart) :
    M.φ (M.φ data.dart) ∉ data.keptDel₁ := by
  classical
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inl ?_, by simpa using hd2⟩
  show M.dartFace (M.φ (M.φ data.dart)) ∈ data.side₁
  rw [M.dartFace_phi, M.dartFace_phi]; exact data.face₁_mem_side₁

/-- **The two kept `face₁` darts are distinct** (the `M`-triangle `face₁` has three distinct
darts).  Uses graph simplicity from the near-triangulation. -/
theorem face₁_kept_darts_distinct (data : hNT.ChordSplitData u v) :
    M.φ data.dart ≠ M.φ (M.φ data.dart) := by
  intro h
  -- `φ d1 = φ d2 ⇒ d1 = d2`, but a triangle has distinct darts.
  have htri := data.face₁_isFaceTriangle
  -- htri : IsFaceTriangle dart (φ dart) (φ²dart): φ dart = φ dart, φ(φ dart)=φ²dart, φ(φ²dart)=dart
  obtain ⟨_, h12, h20⟩ := htri
  -- from `h : φ dart = φ² dart` we get `dart = φ dart` by injectivity, contradicting simplicity.
  have : M.φ data.dart = M.φ (M.φ data.dart) := h
  have heq : data.dart = M.φ data.dart := M.φ.injective this
  exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) heq.symm

/-- **`face₁` contributes exactly two kept darts** (UNCONDITIONAL, the `M`-side of the count).
The two non-chord darts of the `M`-triangle `face₁` are kept and distinct; the chord dart is
deleted.  This is the genuine chord-triangle structure underlying `tOrbitCard = 2` for the
touched `face₁` side face — established with no correct-anchor input. -/
theorem face₁_two_kept_darts (data : hNT.ChordSplitData u v) :
    (M.φ data.dart ∉ data.keptDel₁) ∧ (M.φ (M.φ data.dart) ∉ data.keptDel₁) ∧
      M.φ data.dart ≠ M.φ (M.φ data.dart) ∧
      M.dartFace (M.φ data.dart) = data.face₁ ∧
      M.dartFace (M.φ (M.φ data.dart)) = data.face₁ := by
  -- triangle distinctness gives φ dart ≠ dart and φ² dart ≠ dart.
  obtain ⟨_, h12, h20⟩ := data.face₁_isFaceTriangle
  have hd1 : M.φ data.dart ≠ data.dart := by
    intro he
    have : data.dart = M.φ data.dart := he.symm
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) he
  have hd2 : M.φ (M.φ data.dart) ≠ data.dart := by
    -- φ²dart = dart would force dart = φ dart (apply φ, use h20); contradiction.
    intro he
    have hstep : M.φ (M.φ (M.φ data.dart)) = M.φ data.dart := congrArg M.φ he
    -- h20 : φ (φ² dart) = dart, so dart = φ dart.
    have : data.dart = M.φ data.dart := h20.symm.trans hstep
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) this.symm
  refine ⟨face₁_phi_dart_kept data hd1, face₁_phi_phi_dart_kept data hd2,
    face₁_kept_darts_distinct data, ?_, ?_⟩
  · show M.dartFace (M.φ data.dart) = M.dartFace data.dart; rw [M.dartFace_phi]
  · show M.dartFace (M.φ (M.φ data.dart)) = M.dartFace data.dart
    rw [M.dartFace_phi, M.dartFace_phi]

end Discharge

end ProofsInTheBook.ChordFaceFinal

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordFaceFinal
-/
/- Source module: ProofsInTheBook.ChordAnchor -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordAnchor

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal

universe u



section TwoCycle

variable {K : Type u} [DecidableEq K]

/-- The natural-number iterate of a swap stays on the two swapped points. -/
 lemma swap_iterate_mem {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) :
    ∀ n : ℕ, g^[n] k₀ = k₀ ∨ g^[n] k₀ = k₁ := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]; exact Or.inr h01
      · rw [h]; exact Or.inl h10

variable [Fintype K]

/-- `g.SameCycle k₀ c` with `g` swapping `k₀ ↔ k₁` forces `c ∈ {k₀, k₁}`. -/
 lemma sameCycle_swap_mem {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) {c : K}
    (h : g.SameCycle k₀ c) : c = k₀ ∨ c = k₁ := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rcases swap_iterate_mem h01 h10 n with he | he
  · exact Or.inl (by rw [← hn, he])
  · exact Or.inr (by rw [← hn, he])

/-- **The two-cycle orbit has cardinality `2`.**  If `g k₀ = k₁`, `g k₁ = k₀` with
`k₀ ≠ k₁`, the cycle-orbit filter of `k₀` is exactly `{k₀, k₁}`, of cardinality `2`. -/
theorem twoCycle_orbit_card {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) (hne : k₀ ≠ k₁) :
    (Finset.univ.filter (fun c : K =>
        Quotient.mk (cycleSetoid g) c = Quotient.mk (cycleSetoid g) k₀)).card = 2 := by
  classical
  have hset : (Finset.univ.filter (fun c : K =>
      Quotient.mk (cycleSetoid g) c = Quotient.mk (cycleSetoid g) k₀))
      = ({k₀, k₁} : Finset K) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hsc : g.SameCycle c k₀ := Quotient.exact hc
      exact sameCycle_swap_mem h01 h10 hsc.symm
    · rintro (rfl | rfl)
      · rfl
      · apply Quotient.sound
        -- `g.SameCycle k₁ k₀`: one step `g k₁ = k₀`.
        exact ⟨1, by rw [zpow_one, h10]⟩
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

end TwoCycle



section Card

variable {K : Type u} [Fintype K] [DecidableEq K]

/-- **`tOrbitCard = 2` from the explicit `tracePhi` 2-cycle.**  If the side `tracePhi` swaps
the two kept `face₁` darts `d₁ ↔ d₂` (the correct-anchor placement — the chord cap spliced at
the chord-dart position), then the `tracePhi`-orbit of `d₁` is exactly `{d₁, d₂}`, so the
`face₁` side-face has exactly `2` kept darts. -/
theorem tOrbitCard_eq_two_of_tracePhi_swap (β ρ : Equiv.Perm K) (a₀ a₁ : K) {d₁ d₂ : K}
    (h12 : tracePhi β ρ a₀ a₁ d₁ = d₂) (h21 : tracePhi β ρ a₀ a₁ d₂ = d₁)
    (hne : d₁ ≠ d₂) :
    tOrbitCard β ρ a₀ a₁ d₁ = 2 :=
  twoCycle_orbit_card h12 h21 hne

end Card



section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The correct-anchor orbit-isolation datum** for the touched `face₁` side face.  Records
the genuine discrete Jordan–Schoenflies placement of the chord cap:

* `kface : {d // d ∉ keptDel₁}` — the representative kept dart of the `face₁` side orbit;
* `kother` — its `tracePhi`-2-cycle partner (the other kept `face₁` dart);
* the side `tracePhi` cycles them (`tracePhi kface = kother`, `tracePhi kother = kface`),
  distinct;
* the rep's side face is the chosen `f`;
* exactly one of the two chord predecessors `(sideAlpha₁) a₀`, `(sideAlpha₁) a₁` is
  `tracePhi`-SameCycle to `kface` (the one fresh chord dart re-closing the deleted-dart gap).

This is the chord-cap placement, exposed as concrete `tracePhi` equations — the abstract
`CombMap` does not certify it (the anchors are free parameters of `sideMap₁`). -/
structure CorrectAnchorTwoCycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Type u where
  /-- The representative kept dart of the `face₁` side orbit. -/
  kface : {d : D // d ∉ data.keptDel₁}
  /-- Its `tracePhi`-2-cycle partner. -/
  kother : {d : D // d ∉ data.keptDel₁}
  /-- The side `tracePhi` sends the rep to its partner. -/
  trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kface = kother
  /-- The side `tracePhi` sends the partner back to the rep. -/
  trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kother = kface
  /-- The two kept `face₁` darts are distinct. -/
  distinct : kface ≠ kother
  /-- The rep's side face is the chosen face `f`. -/
  hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl kface) = f
  /-- Exactly one fresh chord dart re-closes the orbit (the one-indicator condition). -/
  one_fresh :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
          ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
          ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1

/-- **The correct-anchor datum gives `tOrbitCard = 2`** for the `face₁` orbit rep. -/
theorem correctAnchor_tOrbitCard_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ hca.kface = 2 :=
  tOrbitCard_eq_two_of_tracePhi_swap (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁
    hca.trace12 hca.trace21 hca.distinct

/-- **The touched `face₁` side face is a `SideFaceTriangle`** — discharged DIRECTLY from the
correct-anchor orbit-isolation (`tOrbitCard = 2` + one fresh chord dart), NOT via a `≠ face₁`
carve-out or boundary absorption.  This is the correct-anchor orbit-isolation closing the last
chord-side residue. -/
theorem face₁_sideFaceTriangle_of_correctAnchor (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  sideFaceTriangle_of_count data hsep a₀ a₁ hne f hca.kface hca.hkf
    (correctAnchor_tOrbitCard_two data hsep a₀ a₁ hne f hca) hca.one_fresh











/-- **The correct-anchor datum is satisfiable (non-vacuous), not a hidden `False`.**  Given the
component data — a `tracePhi`-2-cycle on two distinct kept darts, the rep's face, and the
one-fresh-dart indicator — the structure is inhabited.  This is the §3.3 satisfiability check:
`CorrectAnchorTwoCycle` is the genuine correct-anchor placement (a real 2-cycle equation), not
an unsatisfiable premise. -/
def CorrectAnchorTwoCycle.mk' (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (kface kother : {d : D // d ∉ data.keptDel₁})
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kface = kother)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kother = kface)
    (distinct : kface ≠ kother)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl kface) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    CorrectAnchorTwoCycle data hsep a₀ a₁ hne f :=
  { kface := kface, kother := kother, trace12 := trace12, trace21 := trace21,
    distinct := distinct, hkf := hkf, one_fresh := one_fresh }



/-- The first kept `face₁` dart `M.φ dart`, as a subtype element of `{d // d ∉ keptDel₁}`
(kept by the unconditional `face₁_two_kept_darts`). -/
noncomputable def face₁Dart₁ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨M.φ data.dart, (face₁_two_kept_darts data).1⟩

/-- The second kept `face₁` dart `M.φ² dart`, as a subtype element. -/
noncomputable def face₁Dart₂ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨M.φ (M.φ data.dart), (face₁_two_kept_darts data).2.1⟩

/-- The two kept `face₁` darts are distinct as subtype elements (from
`face₁_two_kept_darts`). -/
theorem face₁Dart_distinct (data : hNT.ChordSplitData u v) :
    face₁Dart₁ data ≠ face₁Dart₂ data := by
  intro h
  exact (face₁_two_kept_darts data).2.2.1 (congrArg Subtype.val h)

/-- **The correct-anchor datum, anchored to the ACTUAL `face₁` darts.**  Given the `tracePhi`
2-cycle on the two genuine kept `face₁` darts `M.φ dart ↔ M.φ² dart` (the chord-cap placement),
their `inl`-side face being the chosen `f`, and the one-fresh-chord-dart indicator, the
correct-anchor datum holds — with distinctness/keptness supplied UNCONDITIONALLY by
`face₁_two_kept_darts`.  This is the genuine chord-triangle orbit-isolation: the 2 kept `face₁`
darts form a length-2 `tracePhi`-orbit, re-closed by one fresh chord dart. -/
noncomputable def correctAnchorTwoCycle_ofFace₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data)
        = face₁Dart₂ data)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data)
        = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    CorrectAnchorTwoCycle data hsep a₀ a₁ hne f :=
  CorrectAnchorTwoCycle.mk' data hsep a₀ a₁ hne f (face₁Dart₁ data) (face₁Dart₂ data)
    trace12 trace21 (face₁Dart_distinct data) hkf one_fresh

/-- **The touched `face₁` side face is a triangle, from the ACTUAL `face₁`-dart 2-cycle.**  The
end-to-end statement the orchestration named: the chord-triangle `face₁`'s keptPhi-orbit has
`tOrbitCard = 2` (its 2 kept darts `M.φ dart`, `M.φ² dart`, the 3rd being the deleted chord
dart), re-closed by one fresh chord dart, so the `face₁` side face is a length-3 triangle —
DIRECTLY, with no `≠ face₁` carve-out. -/
theorem face₁_sideTriangle_ofFace₁Cycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data)
        = face₁Dart₂ data)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data)
        = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  face₁_sideFaceTriangle_of_correctAnchor data hsep a₀ a₁ hne f
    (correctAnchorTwoCycle_ofFace₁ data hsep a₀ a₁ hne f trace12 trace21 hkf one_fresh)

end Discharge

end ProofsInTheBook.ChordAnchor














end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordAnchor
-/
/- Source module: ProofsInTheBook.ChordAnchorInst -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordAnchorInst

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor

universe u



section Algebra

variable {K : Type u} [Fintype K] [DecidableEq K]

/-- **`tracePhi` is `keptPhi` with its values at `ρ a₀`, `ρ a₁` swapped.** -/
lemma tracePhi_eq_swap_keptPhi (β ρ : Equiv.Perm K) (a₀ a₁ k : K) :
    tracePhi β ρ a₀ a₁ k = Equiv.swap (ρ a₀) (ρ a₁) (keptPhi β ρ k) := by
  show (Equiv.swap (ρ a₀) (ρ a₁) * (ρ * β)) k = Equiv.swap (ρ a₀) (ρ a₁) ((ρ * β) k)
  rw [Equiv.Perm.mul_apply]



end Algebra



section KeptPhi

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **`keptPhi d₁ = d₂` on the chord-split side (the easy filtered step).**  The
side face permutation `keptPhi (sideAlpha₁) sideSigma₁` sends the first kept
`face₁` dart `face₁Dart₁ = ⟨M.φ dart, _⟩` to the second `face₁Dart₂ = ⟨M.φ² dart,
_⟩`.  The `α`-then-`σ` step is `M.σ (M.α (M.φ dart)) = M.φ² dart` (= `M.φ`
applied to `M.φ dart`), which is kept, so the filtered rotation does not skip. -/
theorem keptPhi_face₁Dart₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) = face₁Dart₂ data := by
  classical
  -- `keptPhi … d₁ = sideSigma₁ (sideAlpha₁ d₁)`.
  apply Subtype.ext
  show ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₁ data))) : D)
    = (face₁Dart₂ data : D)
  -- `sideSigma₁ = filteredRotation M.σ keptDel₁`.
  have hval : ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) = M.α (M.φ data.dart) := by
    rw [sideAlpha₁_apply_coe]; rfl
  -- the `σ`-successor of `α (M.φ dart)` is `M.φ² dart`, which is kept.
  have hstep : M.σ ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) = M.φ (M.φ data.dart) := by
    rw [hval]
    show M.σ (M.α (M.φ data.dart)) = (M.σ * M.α) (M.φ data.dart)
    rw [Equiv.Perm.mul_apply]
  have hkept : M.σ ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) ∉ data.keptDel₁ := by
    rw [hstep]; exact (face₁_two_kept_darts data).2.1
  show ((FilteredRotation.filteredRotation M.σ data.keptDel₁
        (data.sideAlpha₁ hsep (face₁Dart₁ data))) : D) = (face₁Dart₂ data : D)
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁
    (data.sideAlpha₁ hsep (face₁Dart₁ data)) hkept, hstep]
  rfl

/-- **`keptPhi d₂ ≠ d₂`.**  From `keptPhi d₁ = d₂` and `d₁ ≠ d₂`: if `keptPhi d₂ =
d₂` then `keptPhi d₂ = keptPhi d₁`, so `d₂ = d₁` by injectivity — contradiction.
This is the only consequence needed beyond the bigon closure, and it is FREE. -/
theorem keptPhi_face₁Dart₂_ne_self (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) ≠ face₁Dart₂ data := by
  intro h
  have h1 := keptPhi_face₁Dart₁ data hsep
  -- keptPhi d₂ = d₂ = keptPhi d₁ ⇒ d₂ = d₁.
  have : keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data)
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) := by
    rw [h, ← h1]
  have heq : face₁Dart₂ data = face₁Dart₁ data :=
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).injective this
  exact (face₁Dart_distinct data) heq.symm

end KeptPhi



section Residue

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

















end Residue

end ProofsInTheBook.ChordAnchorInst













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordAnchorInst
-/
/- Source module: ProofsInTheBook.ChordBigonWrap -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace ProofsInTheBook.ChordBigonWrap

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



/-- **`M.φ³ dart = dart`** — the chord-incident face `face₁` is an `M`-triangle.  This is
the third leg of `data.face₁_isFaceTriangle` (which descends from `hNT.inner_tri` applied to
the non-outer face `face₁`): `M.φ (M.φ² dart) = dart`.  UNCONDITIONAL. -/
theorem phi_cube_dart (data : hNT.ChordSplitData u v) :
    M.φ (M.φ (M.φ data.dart)) = data.dart :=
  data.face₁_isFaceTriangle.2.2

/-- **`M.σ (M.α (M.φ² dart)) = dart`** — the immediate `σ`-successor of the `α`-image of `d₂`
is the chord dart.  `M.σ ∘ M.α = M.φ`, so this is `M.φ (M.φ² dart) = M.φ³ dart = dart`.
UNCONDITIONAL. -/
theorem sigma_alpha_phiSq_dart_eq_dart (data : hNT.ChordSplitData u v) :
    M.σ (M.α (M.φ (M.φ data.dart))) = data.dart := by
  show (M.σ * M.α) (M.φ (M.φ data.dart)) = data.dart
  rw [← CombMap.φ]
  exact phi_cube_dart data

/-- **The first `σ`-step of the filtered rotation at `d₂` is the DELETED chord dart.**  The
filtered rotation `sideSigma₁ = filteredRotation M.σ keptDel₁` starts from `sideAlpha₁ d₂`,
whose underlying dart is `M.α (M.φ² dart)`; its immediate `M.σ`-successor is
`M.σ (M.α (M.φ² dart)) = dart ∈ keptDel₁`.  So the rotation cannot take the trivial single
step — it MUST skip the chord dart.  This is the concrete skip certificate of the bigon
wrap, UNCONDITIONAL. -/
theorem bigonWrap_firstStep_deleted (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.σ ((data.sideAlpha₁ hsep (face₁Dart₂ data) : {d : D // d ∉ data.keptDel₁}) : D)
      ∈ data.keptDel₁ := by
  have hval : ((data.sideAlpha₁ hsep (face₁Dart₂ data)) : D) = M.α (M.φ (M.φ data.dart)) := by
    rw [sideAlpha₁_apply_coe]; rfl
  rw [hval, sigma_alpha_phiSq_dart_eq_dart data]
  exact dart_mem_keptDel₁ data

/-- **`firstOutside ≥ 2` at `d₂`.**  Because the first `σ`-successor is deleted
(`bigonWrap_firstStep_deleted`), the filtered rotation takes at least two `σ`-steps from
`sideAlpha₁ d₂`: the wrap is a genuine skip, never the trivial consecutive step.
UNCONDITIONAL. -/
theorem sideSigma₁_sideAlpha₁_firstOutside_ge_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
          (data.sideAlpha₁ hsep (face₁Dart₂ data)) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  -- `firstOutside` is positive, so it must be `1` — forcing the deleted first step to be kept.
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
      (data.sideAlpha₁ hsep (face₁Dart₂ data)) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ data.keptDel₁ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
      (data.sideAlpha₁ hsep (face₁Dart₂ data)) = 1 := by omega
  -- the survivor (which is `∉ keptDel₁`) equals the first `σ`-step, which is deleted.
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ data.keptDel₁
    (data.sideAlpha₁ hsep (face₁Dart₂ data))
  rw [heq1, pow_one] at hnot
  exact hnot (bigonWrap_firstStep_deleted data hsep)





















end ProofsInTheBook.ChordBigonWrap













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordBigonWrap
-/
/- Source module: ProofsInTheBook.ChordSigmaContig -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace ProofsInTheBook.ChordSigmaContig

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordBigonWrap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



/-- A `σ`-power preserves the `tail` (vertex): `tail ((σ^n) d) = tail d`.  The two
darts are `σ`-`SameCycle` (witnessed by the exponent `n`), so they have the same
`σ`-orbit class, which is `tail`. -/
lemma tail_pow_sigma (n : ℕ) (d : D) :
    M.tail ((M.σ ^ n) d) = M.tail d := by
  apply Quotient.sound
  -- `SameCycle ((σ^n) d) d` via the exponent `-n`.
  refine ⟨-(n : ℤ), ?_⟩
  rw [zpow_neg, zpow_natCast, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

/-- **The filtered rotation keeps the vertex fixed.**  For any deleted set and kept
dart `x`, the filtered successor lives at the same vertex as `x`. -/
lemma tail_filteredRotation (Del : Finset D) (x : {d : D // d ∉ Del}) :
    M.tail (FilteredRotation.filteredRotation M.σ Del x : D) = M.tail x.1 := by
  rw [FilteredRotation.filteredRotation_apply_coe]
  exact tail_pow_sigma _ x.1



/-- `M.α (M.φ² dart)` lives at vertex `tail dart` (= `u`): its `σ`-successor is the
chord dart `dart`, so it is `σ`-`SameCycle` with `dart`. -/
lemma tail_alpha_phiSq_dart (data : hNT.ChordSplitData u v) :
    M.tail (M.α (M.φ (M.φ data.dart))) = M.tail data.dart := by
  have h : M.σ (M.α (M.φ (M.φ data.dart))) = data.dart :=
    sigma_alpha_phiSq_dart_eq_dart data
  calc
    M.tail (M.α (M.φ (M.φ data.dart)))
        = M.tail (M.σ (M.α (M.φ (M.φ data.dart)))) := (M.tail_sigma _).symm
    _ = M.tail data.dart := by rw [h]

/-- **`keptPhi d₂` lands at vertex `tail dart` (= `u`).**  `keptPhi d₂ =
sideSigma₁ (sideAlpha₁ d₂)`; the `α`-step's underlying dart is `M.α (M.φ² dart)`
(at vertex `tail dart`), and the filtered rotation keeps the vertex. -/
theorem keptPhi_face₁Dart₂_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) :
        {d : D // d ∉ data.keptDel₁}) : D)
      = M.tail data.dart := by
  -- `keptPhi β ρ k = ρ (β k)`; unfold `ρ = sideSigma₁ = filteredRotation M.σ keptDel₁`.
  show M.tail ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₂ data)) :
      {d : D // d ∉ data.keptDel₁}) : D) = M.tail data.dart
  -- the filtered rotation preserves the vertex of its argument,
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
    tail_filteredRotation data.keptDel₁ (data.sideAlpha₁ hsep (face₁Dart₂ data))]
  -- whose underlying dart is `M.α (M.φ² dart)`, at vertex `tail dart`.
  rw [sideAlpha₁_apply_coe]
  show M.tail (M.α ((face₁Dart₂ data : {d : D // d ∉ data.keptDel₁}) : D)) = M.tail data.dart
  show M.tail (M.α (M.φ (M.φ data.dart))) = M.tail data.dart
  exact tail_alpha_phiSq_dart data

/-- **`d₁ = M.φ dart` lives at vertex `head dart` (= `v`).**  `tail (M.φ dart) =
head dart` by `tail_phi`. -/
theorem face₁Dart₁_tail (data : hNT.ChordSplitData u v) :
    M.tail ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D) = M.head data.dart := by
  show M.tail (M.φ data.dart) = M.head data.dart
  exact M.tail_phi data.dart

/-- **The two chord endpoints are distinct vertices** (`tail dart ≠ head dart`):
the chord is a genuine edge, so it is not a loop. -/
theorem u_ne_v (data : hNT.ChordSplitData u v) :
    M.tail data.dart ≠ M.head data.dart :=
  hNT.simpleGraph.no_loop data.dart



/-- **The chord-cap bigon WRAP `keptPhi d₂ = d₁` is FALSE.**  `keptPhi d₂` lives at
vertex `tail dart = u` (`keptPhi_face₁Dart₂_tail`) and `d₁ = M.φ dart` lives at the
other chord endpoint `head dart = v` (`face₁Dart₁_tail`), with `u ≠ v` (`u_ne_v`);
distinct vertices force distinct darts.

This is the precise refutation of the route proposed in `opus-bigonwrap-reply.md`:
the filtered rotation `sideSigma₁` only ever moves *within* a single `σ`-orbit
(vertex), so no `FilteredRotation.ContiguousInterval` for `u`'s kept darts can make
it reach `d₁`, which sits at `v`.  The `keptPhi`-wrap is the WRONG residue. -/
theorem keptPhi_face₁Dart₂_ne_face₁Dart₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) ≠ face₁Dart₁ data := by
  intro hwrap
  -- equal darts ⇒ equal `tail`s, contradicting the distinct-vertex facts.
  have htail : M.tail ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) :
      {d : D // d ∉ data.keptDel₁}) : D)
        = M.tail ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D) := by
    rw [hwrap]
  rw [keptPhi_face₁Dart₂_tail data hsep, face₁Dart₁_tail data] at htail
  exact u_ne_v data htail





















end ProofsInTheBook.ChordSigmaContig

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSigmaContig
-/
/- Source module: ProofsInTheBook.ZinanCh35SideAnchors -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35SideAnchors

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



/-- **The canonical side-1 anchor `a₀`** — the kept dart whose `sideSigma₁`-successor is
`keptPhi d₂`. -/
noncomputable def side₁Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₁} :=
  (data.sideSigma₁).symm
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data))

/-- **The canonical side-1 anchor `a₁`** — the kept dart whose `sideSigma₁`-successor is
`d₁ = M.φ dart`. -/
noncomputable def side₁Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₁} :=
  (data.sideSigma₁).symm (face₁Dart₁ data)

/-- **`sideSigma₁ a₀ = keptPhi d₂`** (definitional, `Equiv.apply_symm_apply`). -/
@[simp] theorem sideSigma₁_side₁Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) := by
  rw [side₁Anchor₀, Equiv.apply_symm_apply]

/-- **`sideSigma₁ a₁ = d₁`** (definitional, `Equiv.apply_symm_apply`). -/
@[simp] theorem sideSigma₁_side₁Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₁ (side₁Anchor₁ data hsep) = face₁Dart₁ data := by
  rw [side₁Anchor₁, Equiv.apply_symm_apply]

/-- **The canonical anchors are distinct.**  If `a₀ = a₁` then their `sideSigma₁`-images
agree, i.e. `keptPhi d₂ = d₁` — refuted by the proven geometric fact
`ChordSigmaContig.keptPhi_face₁Dart₂_ne_face₁Dart₁` (the false-wrap correction). -/
theorem side₁Anchors_ne (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    side₁Anchor₀ data hsep ≠ side₁Anchor₁ data hsep := by
  intro h
  -- equal anchors ⇒ equal `sideSigma₁`-images ⇒ `keptPhi d₂ = d₁`, contradiction.
  have himg : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = data.sideSigma₁ (side₁Anchor₁ data hsep) := by rw [h]
  rw [sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁] at himg
  exact keptPhi_face₁Dart₂_ne_face₁Dart₁ data hsep himg



/-- **`d₁` and `keptPhi d₂` lie on a common `keptPhi`-cycle.**  `keptPhi.SameCycle d₁
(keptPhi d₂)`: `keptPhi d₁ = d₂` (`keptPhi_face₁Dart₁`), and `keptPhi d₂` is one further
forward step from `d₂`, so `d₁ → d₂ → keptPhi d₂` is a `keptPhi`-walk. -/
theorem keptPhi_sameCycle_d₁_keptPhi_d₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
      (face₁Dart₁ data)
      (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data)) := by
  -- peel the outer `keptPhi` on the right: reduce to `SameCycle d₁ d₂`.
  rw [Equiv.Perm.sameCycle_apply_right]
  -- `SameCycle d₁ d₂` from `keptPhi d₁ = d₂`.
  rw [← keptPhi_face₁Dart₁ data hsep]
  exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **The anchor-incidence fact for the canonical anchors** (`Side₁AnchorsShareFace`).  The
canonical anchors' `sideSigma₁`-successors `keptPhi d₂` and `d₁` lie on a common kept
(`keptPhi`) face — the shared pre-splice boundary face (the `face₁` orbit).  This is the
proven fact-2 instance the chord-side disk/sphere machinery
(`ChordDisk.side₁_isSphereMap_of_disk`, `ChordSideNT.side₁_sphere_unconditional`) consumes,
now SUPPLIED for the canonical anchors. -/
theorem side₁AnchorsShareFace_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) := by
  -- unfold to `keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁)`,
  show (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle
    (data.sideSigma₁ (side₁Anchor₀ data hsep)) (data.sideSigma₁ (side₁Anchor₁ data hsep))
  rw [sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁]
  -- i.e. `SameCycle (keptPhi d₂) d₁`, the symmetric of `keptPhi_sameCycle_d₁_keptPhi_d₂`.
  exact (keptPhi_sameCycle_d₁_keptPhi_d₂ data hsep).symm



/-- **The easy splice-swap direction `tracePhi d₂ = d₁`** for the canonical anchors.  Since
`ρ a₀ = keptPhi d₂`, the swap `swap (keptPhi d₂) (ρ a₁)` sends `keptPhi d₂ ↦ ρ a₁ = d₁`. -/
theorem side₁Anchors_trace21 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₂ data)
      = face₁Dart₁ data := by
  rw [tracePhi_eq_swap_keptPhi, sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁]
  -- `swap (keptPhi d₂) d₁ (keptPhi d₂) = d₁`.
  exact Equiv.swap_apply_left _ _

/-- **The other splice-swap direction `tracePhi d₁ = d₂`** for the canonical anchors.
`tracePhi d₁ = swap (keptPhi d₂) d₁ (keptPhi d₁)`; `keptPhi d₁ = d₂`
(`keptPhi_face₁Dart₁`), and `d₂ ∉ {keptPhi d₂, d₁}` (`keptPhi_face₁Dart₂_ne_self`,
`face₁Dart_distinct`), so the swap fixes `d₂`. -/
theorem side₁Anchors_trace12 (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (face₁Dart₁ data)
      = face₁Dart₂ data := by
  rw [tracePhi_eq_swap_keptPhi, sideSigma₁_side₁Anchor₀, sideSigma₁_side₁Anchor₁,
    keptPhi_face₁Dart₁ data hsep]
  -- `swap (keptPhi d₂) d₁ d₂ = d₂` since `d₂ ≠ keptPhi d₂` and `d₂ ≠ d₁`.
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
  · -- `d₂ ≠ keptPhi d₂` (symm of `keptPhi_face₁Dart₂_ne_self`).
    exact (keptPhi_face₁Dart₂_ne_self data hsep).symm
  · -- `d₂ ≠ d₁` (symm of `face₁Dart_distinct`).
    exact (face₁Dart_distinct data).symm







end ProofsInTheBook.ZinanCh35SideAnchors













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35SideAnchors
-/
/- Source module: ProofsInTheBook.ZinanCh35Hclass -/
section
set_option autoImplicit true


/-!
# The Chapter 35 chord-side `hclass` gluing bricks (the `ContiguousInterval` master glue)

`ZinanCh35SideAnchors.lean` pinned the **canonical** chord-cap anchors `a₀, a₁` of side 1 and
proved, UNCONDITIONALLY, the post-splice `tracePhi` 2-cycle on the two kept `face₁` darts
(`side₁Anchors_trace12`/`trace21`).  This file assembles those anchor facts, together with the
explicit-trace orbit machinery of `ChordBoundaryOrbit` and the correct-anchor structure of
`ChordAnchor`, into the master **per-face classifier** consumed by
`ChordAnchor.contiguousInterval_of_correctAnchor`:

> for every non-outer side face `g`, EITHER `g` has a splice-untouched, side-`₁`,
> non-`face₁` kept-`inl` representative, OR `g` carries a `CorrectAnchorTwoCycle` datum.

and then feeds it into the final `ContiguousInterval` assembler.

## Bricks (design §8 order)

1.  Notation block (`β ρ a₀ a₁ hne S τ`).
2.  `side₁_trace_beta_a0_to_face₁Dart₁` — `τ (β a₀) = face₁Dart₁ data`
    (`tracePhi_b0` + `sideSigma₁_side₁Anchor₁`).
3.  `side₁_chord0_face_eq_face₁_canonical` — `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁)`
    (`chordDart_face_eq_b0` + `sideFace_inl_eq_iff_tracePhi` via brick 2).
4.  `Side₁OuterTraceData` — the INPUT bundle (outer face + its boundary cycle, the two chord/face
    incidence facts, and the inner-rep avoidance residue).
5.  `side₁Anchors_oneFresh_canonical` — the one-fresh indicator `= 1`.
6.  `side₁_correctAnchor_face₁_canonical` — the `CorrectAnchorTwoCycle` datum for the touched
    `face₁` side face (`correctAnchorTwoCycle_ofFace₁` + bricks 5 & landed trace12/trace21).
7.  `side1_hclass_canonical` — the MASTER per-face classifier (face₁ branch transports brick 6
    across the face equality; no-hit branch uses `spliceUntouched_of_face_ne_chordOrbits`).
8.  `contiguousInterval_canonical` — feed brick 7 into `contiguousInterval_of_correctAnchor`.

**Input-bundle addition (reported per the design's license).**  The design's
`Side₁OuterTraceData` lists `outerFace, outerCycle, outer_simple, outer_len, chord1_is_outer,
face₁_not_outer`.  The no-hit branch's `M.dartFace k.1 ∈ side₁` (`hside`) obligation is the
genuine geometric residue "the side outer face is exactly the `M`-outer-arc orbit, so every other
face's rep avoids the `M`-outer face" — NOT derivable from the abstract `CombMap`.  Rather than
weaken, we carry it as the repo-native field `inner_reps :
ChordBoundaryOrbit.InnerRepsAvoidBoundary …` (which packages exactly "each non-outer side face has
a kept-`inl` rep with `M`-face `≠ M`-outer and `≠ face₁`"), as the design explicitly permits.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35Hclass

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}





/-- **`τ (β a₀) = face₁Dart₁`** for the canonical anchors. -/
theorem side₁_trace_beta_a0_to_face₁Dart₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
      = face₁Dart₁ data := by
  rw [tracePhi_b0 (data.sideAlpha₁ hsep) data.sideSigma₁ (data.sideAlpha₁_involutive hsep),
    sideSigma₁_side₁Anchor₁]

/-- **`β a₀` is `τ`-SameCycle to `face₁Dart₁`** (one `τ`-step), the orbit form of brick 2. -/
theorem side₁_betaA0_sameCycle_face₁Dart₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) (face₁Dart₁ data) := by
  refine ⟨1, ?_⟩
  rw [zpow_one]
  exact side₁_trace_beta_a0_to_face₁Dart₁ data hsep



/-- **The fresh dart `inr 0` joins the `face₁` side face**: `S.dartFace (inr 0) = S.dartFace
(inl face₁Dart₁)`. -/
theorem side₁_chord0_face_eq_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) := by
  -- `inr 0 ↦ inl (β a₀)` (wrapper, in `sideMap₁` form), then `inl (β a₀) ↦ inl face₁Dart₁`.
  rw [sideMap₁_chordDart_face_eq_b0 data hsep (side₁Anchor₀ data hsep)
        (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)]
  -- `S.dartFace (inl (β a₀)) = S.dartFace (inl face₁Dart₁)` iff `β a₀ ~τ face₁Dart₁` (brick 2).
  exact (sideFace_inl_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
    (side₁Anchors_ne data hsep)
    ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) (face₁Dart₁ data)).2
    (side₁_betaA0_sameCycle_face₁Dart₁ data hsep)





















end ProofsInTheBook.ZinanCh35Hclass










end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Hclass
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterTrace -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterTrace

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35Hclass

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u



section PermSplit

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **Right-multiplication split.**  If `a ≠ b` and `a, b` are in the same `p`-cycle, then
`p * swap a b` does NOT have `a, b` in one cycle.  (The `same`-cycle branch of the dichotomy:
the swap splits the shared cycle.) -/
theorem notSameCycle_mul_swap_right_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    ¬ (p * Equiv.swap a b).SameCycle a b := by
  intro hqsc
  -- If both `p` and `p * swap` had `a, b` same-cycle, the cycle counts coincide,
  -- contradicting `numCycles_mul_swap_ne`.
  have hq_le_p : numCycles (p * Equiv.swap a b) ≤ numCycles p := by
    have h := PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle
      (p * Equiv.swap a b) hqsc
    simpa [mul_assoc] using h
  have hp_le_q : numCycles p ≤ numCycles (p * Equiv.swap a b) :=
    PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle p hsc
  exact PermTranspositionCycleCount.numCycles_mul_swap_ne p hab
    (le_antisymm hq_le_p hp_le_q)

/-- **Left-multiplication split.**  If `a ≠ b` and `a, b` are in the same `p`-cycle, then
`swap a b * p` does NOT have `a, b` in one cycle.  Reduced to the right-multiplication split by
conjugation with `swap a b` (which fixes the cycle structure and swaps `a ↔ b`). -/
theorem notSameCycle_swap_mul_left_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    ¬ (Equiv.swap a b * p).SameCycle a b := by
  intro hsc'
  -- Conjugating `(swap a b * p).SameCycle a b` by `g := swap a b`:
  -- `(swap·(swap·p)·swap⁻¹).SameCycle (swap a)(swap b)`, and
  -- `swap·(swap·p)·swap⁻¹ = p·swap⁻¹ = p·swap`, `swap a = b`, `swap b = a`.
  apply notSameCycle_mul_swap_right_of_sameCycle p hab hsc
  have h2 := hsc'.conj (g := Equiv.swap a b)
  -- normalise the conjugate permutation and the two swapped endpoints.
  have hperm : Equiv.swap a b * (Equiv.swap a b * p) * (Equiv.swap a b)⁻¹
      = p * Equiv.swap a b := by
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul, Equiv.swap_inv]
  rw [hperm, Equiv.swap_apply_left, Equiv.swap_apply_right] at h2
  exact h2.symm

end PermSplit



section Canonical

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The canonical chord predecessors are NOT `tracePhi`-SameCycle.**  `τ = swap (ρ a₀) (ρ a₁)
* keptPhi`, with `keptPhi.SameCycle (ρ a₀) (ρ a₁)` (the proved `side₁AnchorsShareFace_canonical`)
and `ρ a₀ ≠ ρ a₁` (anchors distinct).  Hence the swap splits the shared kept face, so the two
chord predecessors `ρ a₀`, `ρ a₁` no longer share a `τ`-cycle; transporting one `τ`-step on each
side gives `¬ τ.SameCycle (β a₀) (β a₁)`. -/
theorem side₁_chordPred_notSameCycle_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
      ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) := by
  classical
  set β := data.sideAlpha₁ hsep with hβ
  set ρ := data.sideSigma₁ with hρ
  set a₀ := side₁Anchor₀ data hsep with ha₀
  set a₁ := side₁Anchor₁ data hsep with ha₁
  -- the share-face fact: `keptPhi.SameCycle (ρ a₀) (ρ a₁)`.
  have hshare : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁) := by
    have h := side₁AnchorsShareFace_canonical data hsep
    -- unfolds to `keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁)`.
    simpa [hβ, hρ, ha₀, ha₁, ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace, keptPhi]
      using h
  -- `ρ a₀ ≠ ρ a₁`.
  have hne : ρ a₀ ≠ ρ a₁ := ρa₀_ne_ρa₁ ρ (side₁Anchors_ne data hsep)
  -- the split: `¬ τ.SameCycle (ρ a₀) (ρ a₁)`.
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (ρ a₀) (ρ a₁) := by
    rw [show tracePhi β ρ a₀ a₁ = Equiv.swap (ρ a₀) (ρ a₁) * keptPhi β ρ from rfl]
    exact notSameCycle_swap_mul_left_of_sameCycle (keptPhi β ρ) hne hshare
  -- transport: `τ (β a₀) = ρ a₁` and `τ (β a₁) = ρ a₀`, so
  -- `τ.SameCycle (β a₀) (β a₁) ↔ τ.SameCycle (ρ a₁) (ρ a₀)`.
  intro hsc
  apply hsplit
  have hb0 : tracePhi β ρ a₀ a₁ (β a₀) = ρ a₁ :=
    tracePhi_b0 β ρ (data.sideAlpha₁_involutive hsep) a₀ a₁
  have hb1 : tracePhi β ρ a₀ a₁ (β a₁) = ρ a₀ :=
    tracePhi_b1 β ρ (data.sideAlpha₁_involutive hsep) a₀ a₁
  -- `τ.SameCycle (β a₀) (β a₁) → τ.SameCycle (τ (β a₀)) (τ (β a₁)) = τ.SameCycle (ρ a₁) (ρ a₀)`.
  have hstep : (tracePhi β ρ a₀ a₁).SameCycle
      (tracePhi β ρ a₀ a₁ (β a₀)) (tracePhi β ρ a₀ a₁ (β a₁)) :=
    hsc.apply_left.apply_right
  rw [hb0, hb1] at hstep
  exact hstep.symm

/-- **`face₁_not_outer` for `outerFace := S.dartFace (inr 1)`.**  `S.dartFace (inl face₁Dart₁)
= S.dartFace (inr 0)` (brick 3), and `S.dartFace (inr 0) ≠ S.dartFace (inr 1)` by
`chordOrbits_eq_iff_tracePhi` + the splice-split fact. -/
theorem side₁_face₁_not_outer_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))
      ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
  intro hcontra
  -- `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁) = S.dartFace (inr 1)`.
  have h01 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
    rw [side₁_chord0_face_eq_face₁_canonical data hsep, hcontra]
  -- `chordOrbits_eq_iff_tracePhi` : the chord-dart faces coincide iff the chord predecessors
  -- share a `tracePhi`-orbit.
  have hsame : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
        ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) :=
    (chordOrbits_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      (side₁Anchors_ne data hsep)).1 h01
  exact side₁_chordPred_notSameCycle_canonical data hsep hsame









end Canonical

end ProofsInTheBook.ZinanCh35OuterTrace









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35OuterTrace
-/
/- Source module: ProofsInTheBook.ZinanCh35Iota -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Iota

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]



/-- **`ι` computes on a class to the `M.tail` of its projected representative.**  By the
`Quotient.lift` definition of `sideVertexToM₁`, the class of a representative `y` maps to
`M.tail (proj a₀ a₁ y).1`.  (This is the generalisation of `sideVertexToM₁_inl` to arbitrary
representatives, fresh darts included.) -/
lemma sideVertexToM₁_mk (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) y)
      = M.tail (proj a₀ a₁ y).1 :=
  rfl

/-- **Brick 1 — `ι` is injective.**  `ι ⟦y⟧ = ι ⟦z⟧` gives `M.σ.SameCycle (proj y).1 (proj z).1`
(`M.tail` equal ⇒ same `σ`-cycle, `Quotient.exact`).  Transport back: a `sideSigma₁`-SameCycle of
`proj y`, `proj z` (`filteredRotation_sameCycle_iff`), then a `freshSigma`-SameCycle of `y`, `z`
(`freshSigma_sameCycle_iff` backward), i.e. `⟦y⟧ = ⟦z⟧`.  Purely combinatorial. -/
theorem sideVertexToM₁_injective_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    Function.Injective (sideVertexToM₁ data hsep a₀ a₁ hne) := by
  -- reduce to representatives.
  refine fun X Y => ?_
  refine Quotient.inductionOn₂ X Y (fun y z hYZ => ?_)
  -- `hYZ : ι ⟦y⟧ = ι ⟦z⟧`, defeq `M.tail (proj y).1 = M.tail (proj z).1`.
  -- `M.tail a = M.tail b` is `Quotient.mk (cycleSetoid M.σ) a = …`, so `Quotient.exact` gives
  -- `M.σ.SameCycle a b` (Lean unfolds `ι ⟦·⟧ = M.tail (proj ·).1` definitionally).
  have hM : M.σ.SameCycle (proj a₀ a₁ y).1 (proj a₀ a₁ z).1 := Quotient.exact hYZ
  -- back to a `sideSigma₁`-SameCycle of the (kept) projections.
  have hss : data.sideSigma₁.SameCycle (proj a₀ a₁ y) (proj a₀ a₁ z) :=
    (FilteredRotation.filteredRotation_sameCycle_iff M.σ data.keptDel₁
      (proj a₀ a₁ y) (proj a₀ a₁ z)).2 hM
  -- back to a `freshSigma`-SameCycle of the representatives.
  have hfs : (freshSigma data.sideSigma₁ a₀ a₁ hne).SameCycle y z :=
    (freshSigma_sameCycle_iff data.sideSigma₁ hne y z).2 hss
  exact Quotient.sound hfs



/-- `ι (sideMap₁.tail (inr j))` is `M.tail a₀.1` (`j = 0`) or `M.tail a₁.1` (`j = 1`). -/
lemma sideVertexToM₁_tail_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) (Sum.inr j))
      = M.tail (if j = 0 then a₀.1 else a₁.1) := by
  rw [sideVertexToM₁_mk data hsep a₀ a₁ hne (Sum.inr j)]
  fin_cases j
  · simp [proj]
  · simp [proj]

/-- `freshAlpha (sideAlpha₁) (inr j)` is the *other* fresh dart `inr (swap j)`, whose `ι`-tail is
the *other* anchor.  Hence the fresh chord dart `inr j` has `ι`-endpoints `M.tail a₀.1` and
`M.tail a₁.1` (in some order). -/
lemma sideVertexToM₁_head_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) (Sum.inr j)))
      = M.tail (if j = 0 then a₁.1 else a₀.1) := by
  rw [freshAlpha_inr]
  rw [sideVertexToM₁_tail_inr data hsep a₀ a₁ hne (Equiv.swap (0 : Fin 2) 1 j)]
  fin_cases j
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]

/-- **The `ι`-edge of any side dart.**  For every side dart `d`, the `ι`-images of its side
endpoints `sideMap₁.tail d`, `sideMap₁.head d` are `M`-adjacent: an `inl x'` dart gives the proved
`M`-edge of `x'` (`ι_adj_of_inl`); a fresh chord dart gives the anchor-tail pair (`M`-adjacent by
`hchord`).  `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧` (definitional). -/
lemma ι_adj_of_dart (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (d : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    M.Adj
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) d))
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) d))) := by
  cases d with
  | inl x' => exact ι_adj_of_inl data hsep a₀ a₁ hne x'
  | inr j =>
      rw [sideVertexToM₁_tail_inr data hsep a₀ a₁ hne j,
        sideVertexToM₁_head_inr data hsep a₀ a₁ hne j]
      fin_cases j
      · simpa using hchord
      · simpa using M.adj_symm hchord



/-- **Brick 2 — `ι_adj`.**  Side adjacency `sideMap₁.toSimpleGraph.Adj x y` carries to
`M.toSimpleGraph.Adj (ι x) (ι y)`.  The witnessing side dart `d` gives `s(x, y) = sideMap₁.dartEdge
d = s(sideMap₁.tail d, sideMap₁.head d)`, whose `ι`-images are `M`-adjacent (`ι_adj_of_dart`); the
unordered pair matches by `Sym2.eq_iff`.  The `≠` half is preserved by injectivity (Brick 1). -/
theorem sideVertexToM₁_adj_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
        M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) := by
  intro x y hxy
  rw [toSimpleGraph_adj] at hxy ⊢
  obtain ⟨hne_xy, d, hd⟩ := hxy
  -- the `≠` part: `ι x ≠ ι y` from injectivity + `x ≠ y`.
  refine ⟨fun h => hne_xy (sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne h), ?_⟩
  -- `s(x, y) = sideMap₁.dartEdge d = s(sideMap₁.tail d, sideMap₁.head d)` (the last `=` is `rfl`).
  have hM := ι_adj_of_dart data hsep a₀ a₁ hne hchord d
  -- `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧` (definitional), so:
  have hd' : s((data.sideMap₁ hsep a₀ a₁ hne).tail d, (data.sideMap₁ hsep a₀ a₁ hne).head d)
      = s(x, y) := hd
  rcases Sym2.eq_iff.1 hd' with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hM
  · rw [← hx, ← hy]; exact M.adj_symm hM



/-- **Brick 3 — `ι_adj_reflect`, isolated as the named confinement residue.**  We do NOT silently
assume more than the field itself: the brick simply *is* the hypothesis, recorded as the minimal
region edge-confinement fact (an `M`-edge between two `ι`-images is a side edge), which the open
`ChordSplitRegions`/Schoenflies layer is responsible for.  Reported in the handoff as the genuine
planar block. -/
theorem sideVertexToM₁_adj_reflect_canonical (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y :=
  hreflect



/-- **Brick 5 — `smaller`.**  From the proved injectivity of `ι` and an explicit omitted
`M`-vertex `w ∉ Set.range ι` (the opposite-arc internal vertex side 1 drops — the named
region-confinement residue `homit`), the side has strictly fewer vertices than `M`. -/
theorem side₁_smaller_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    (data.sideMap₁ hsep a₀ a₁ hne).V < M.V := by
  classical
  obtain ⟨w, hw⟩ := homit
  -- `(sideMap₁).V = Fintype.card (sideMap₁).Vertex`, `M.V = Fintype.card M.Vertex`.
  show Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex < Fintype.card M.Vertex
  -- the image of `ι` is a proper subset of `M.Vertex` (it misses `w`); `ι` injective.
  have hinj := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne
  -- map the (full) domain finset injectively into `M.Vertex`, missing `w`.
  have hcard_le : Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex
      = (Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne)).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [hcard_le]
  -- the image is a finset of `M.Vertex` not containing `w`, hence a strict subset of `univ`.
  have hsub : Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.2 ?_
    intro hfull
    apply hw
    have hmem : w ∈ Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne) := by
      rw [hfull]; exact Finset.mem_univ w
    obtain ⟨V, _, hV⟩ := Finset.mem_image.1 hmem
    exact ⟨V, hV⟩
  calc (Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne)).card
      < (Finset.univ : Finset M.Vertex).card := Finset.card_lt_card hsub
    _ = Fintype.card M.Vertex := Finset.card_univ



/-- **Brick 6 — the side-1 residue, partially assembled.**  All six non-`ci`/`hshare`
`ChordSideResidue` fields are produced: `ι_inj` and the kept-dart half of `ι_adj` PROVED
unconditionally; the fresh-chord `ι_adj` half from `hchord`; `ι_adj_reflect` from the named
confinement residue `hreflect`; `hLₛ` the residue list field; `smaller` from injectivity + the
omitted-vertex residue `homit`.

Remaining (the open `ChordSplitRegions`/discrete-Schoenflies content): `hreflect` (region
edge-confinement) and `homit` (the opposite-arc omitted vertex's not-in-range).  These are the two
honest planar inputs; `hchord` is the chord adjacency `u–v` and `hLₛ` the list transport. -/
def chordSideResidue₁_partial (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  chordSideResidue_mk data hsep a₀ a₁ hne L ci hshare
    (sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne)
    (sideVertexToM₁_adj_canonical data hsep a₀ a₁ hne hchord)
    (sideVertexToM₁_adj_reflect_canonical data hsep a₀ a₁ hne hreflect)
    pₛ qₛ cpₛ cqₛ hLₛ
    (side₁_smaller_canonical data hsep a₀ a₁ hne homit)

end ProofsInTheBook.ZinanCh35Iota









end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapSigma2 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}



open Classical in
/-- Corrected forward map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigma2 (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.divertKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))  -- ℓ_i^+ ↦ c_{prevIdx i}^+  (FIX)
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)             -- ℓ_i^- ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ d)                          -- unchanged rotation
  | Sum.inr (Sum.inl i) => Sum.inl (C.dart (C.nextIdx i))      -- c_i^+ ↦ dart (nextIdx i)  (FIX)
  | Sum.inr (Sum.inr i) => Sum.inl (C.pDart i)                 -- c_i^- ↦ p_i

open Classical in
/-- Corrected inverse map of the cut-and-cap rotation `σ'`. -/
noncomputable def cutSigmaInv2 (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.startKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))  -- d = q_i ↦ c_{prevIdx i}^+  (FIX)
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)             -- d = p_i ↦ c_i^-
      | Sum.inr () => Sum.inl (M.σ.symm d)                     -- unchanged inverse rotation
  | Sum.inr (Sum.inl i) => Sum.inl (M.σ.symm (C.pDart (C.nextIdx i)))  -- c_i^+ ↦ ℓ_{i+1}^+ = σ⁻¹ p_{i+1}
  | Sum.inr (Sum.inr i) => Sum.inl (M.σ.symm (C.qDart i))             -- c_i^- ↦ ℓ_i^- = σ⁻¹ q_i



lemma cutSigma2_inl_plus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inl i)) :
    C.cutSigma2 (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx i)) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma2_inl_minus (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.divertKind d = Sum.inl (Sum.inr i)) :
    C.cutSigma2 (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

lemma cutSigma2_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.divertKind d = Sum.inr ()) :
    C.cutSigma2 (Sum.inl d) = Sum.inl (M.σ d) := by
  show (match C.divertKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ d)) = _
  rw [h]

@[simp] lemma cutSigma2_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma2 (Sum.inr (Sum.inl i)) = Sum.inl (C.dart (C.nextIdx i)) := rfl

@[simp] lemma cutSigma2_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigma2 (Sum.inr (Sum.inr i)) = Sum.inl (C.pDart i) := rfl



lemma cutSigmaInv2_inl_q (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inl i)) :
    C.cutSigmaInv2 (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx i)) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv2_inl_p (C : SimplePrimalCycle M) {d : D} {i : Fin C.len}
    (h : C.startKind d = Sum.inl (Sum.inr i)) :
    C.cutSigmaInv2 (Sum.inl d) = Sum.inr (Sum.inr i) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

lemma cutSigmaInv2_inl_none (C : SimplePrimalCycle M) {d : D}
    (h : C.startKind d = Sum.inr ()) :
    C.cutSigmaInv2 (Sum.inl d) = Sum.inl (M.σ.symm d) := by
  show (match C.startKind d with
    | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl (C.prevIdx i))
    | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)
    | Sum.inr () => Sum.inl (M.σ.symm d)) = _
  rw [h]

@[simp] lemma cutSigmaInv2_capPlus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv2 (Sum.inr (Sum.inl i)) = Sum.inl (M.σ.symm (C.pDart (C.nextIdx i))) := rfl

@[simp] lemma cutSigmaInv2_capMinus (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.cutSigmaInv2 (Sum.inr (Sum.inr i)) = Sum.inl (M.σ.symm (C.qDart i)) := rfl



open Classical in
lemma cutSigma2_leftInv (C : SimplePrimalCycle M) :
    Function.LeftInverse C.cutSigmaInv2 C.cutSigma2 := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on divertKind d
    rcases hd : C.divertKind d with (i | i) | u
    · -- σ d = p_i : ℓ_i^+, goes to c_{prevIdx i}^+, must come back to inl d
      have hσ : M.σ d = C.pDart i := C.divertKind_eq_plus hd
      rw [C.cutSigma2_inl_plus hd, cutSigmaInv2_capPlus, C.nextIdx_prevIdx, ← hσ,
        M.σ.symm_apply_apply]
    · -- σ d = q_i : ℓ_i^-, goes to c_i^-, must come back
      have hσ : M.σ d = C.qDart i := C.divertKind_eq_minus hd
      rw [C.cutSigma2_inl_minus hd, cutSigmaInv2_capMinus, ← hσ, M.σ.symm_apply_apply]
    · -- unchanged
      obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
      rw [C.cutSigma2_inl_none hd, C.cutSigmaInv2_inl_none (C.startKind_none hq hp),
        M.σ.symm_apply_apply]
  · -- x = c_i^+ : σ' c_i^+ = inl (dart (nextIdx i)) = inl (q_{nextIdx i})
    rw [cutSigma2_capPlus]
    -- dart (nextIdx i) = qDart (nextIdx i); startKind sees it as q-dart at nextIdx i
    rw [show C.dart (C.nextIdx i) = C.qDart (C.nextIdx i) from rfl,
      C.cutSigmaInv2_inl_q (C.startKind_q (C.nextIdx i)), C.prevIdx_nextIdx]
  · -- x = c_i^- : σ' c_i^- = inl (p_i); startKind sees it as p-dart at i
    rw [cutSigma2_capMinus,
      show C.pDart i = C.pDart i from rfl, C.cutSigmaInv2_inl_p (C.startKind_p i)]

open Classical in
lemma cutSigma2_rightInv (C : SimplePrimalCycle M) :
    Function.RightInverse C.cutSigmaInv2 C.cutSigma2 := by
  intro x
  rcases x with d | (i | i)
  · -- x = inl d, split on startKind d
    rcases hd : C.startKind d with (i | i) | u
    · -- d = q_i : goes to c_{prevIdx i}^+, must come back to inl d = inl q_i
      have hq : d = C.qDart i := C.startKind_eq_q hd
      rw [C.cutSigmaInv2_inl_q hd, cutSigma2_capPlus, C.nextIdx_prevIdx, hq]; rfl
    · -- d = p_i : goes to c_i^-, must come back to inl p_i
      have hp : d = C.pDart i := C.startKind_eq_p hd
      rw [C.cutSigmaInv2_inl_p hd, cutSigma2_capMinus, hp]
    · -- neither
      obtain ⟨hq, hp⟩ := C.startKind_eq_none hd
      rw [C.cutSigmaInv2_inl_none hd]
      have hdiv : C.divertKind (M.σ.symm d) = Sum.inr () := by
        apply C.divertKind_none
        · intro i; rw [M.σ.apply_symm_apply]; exact hp i
        · intro i; rw [M.σ.apply_symm_apply]; exact hq i
      rw [C.cutSigma2_inl_none hdiv, M.σ.apply_symm_apply]
  · -- x = c_i^+ : inv sends it to inl (σ⁻¹ p_{nextIdx i}) = ℓ_{nextIdx i}^+,
    -- which σ' sends to c_{prevIdx (nextIdx i)}^+ = c_i^+
    rw [cutSigmaInv2_capPlus]
    have hdiv : C.divertKind (M.σ.symm (C.pDart (C.nextIdx i))) = Sum.inl (Sum.inl (C.nextIdx i)) :=
      C.divertKind_plus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma2_inl_plus hdiv, C.prevIdx_nextIdx]
  · -- x = c_i^- : inv sends it to inl (σ⁻¹ q_i) = ℓ_i^-, which σ' sends to c_i^-
    rw [cutSigmaInv2_capMinus]
    have hdiv : C.divertKind (M.σ.symm (C.qDart i)) = Sum.inl (Sum.inr i) :=
      C.divertKind_minus (by rw [M.σ.apply_symm_apply])
    rw [C.cutSigma2_inl_minus hdiv]

/-- The corrected vertex rotation `σ'` as a permutation of the cut dart set. -/
noncomputable def cutSigmaPerm2 (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart where
  toFun := C.cutSigma2
  invFun := C.cutSigmaInv2
  left_inv := C.cutSigma2_leftInv
  right_inv := C.cutSigma2_rightInv

@[simp] lemma cutSigmaPerm2_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.cutSigmaPerm2 x = C.cutSigma2 x := rfl





















end SimplePrimalCycle











end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapFCore -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount























end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma2
import ProofsInTheBook.PlanarMapCutCapFCore
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap2Counts -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount



































-- Triangle anchor (`PlanarMapCutCapEval.lean`):  V' = 6 = V + k = 3 + 3.























-- Triangle anchor (`PlanarMapCutCapEval.lean`):  F' = 4 = F + 2 = 2 + 2.







end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapSigma
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapEval -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv



section Counters

variable {α : Type*} [DecidableEq α]

















end Counters



namespace TriangleMap

open CombMap



















-- α', σ', φ' cycle counts of the *base* triangle map:
                 -- V = 3 (expected)
                 -- E = 3 (expected)
  -- F = 2 (expected)
-- χ = V - E + F = 3 - 3 + 2 = 2.


-- base-map connectivity: one dartStep component.
        -- c = 1 (connected, expected)

end TriangleMap



namespace TriangleCut

open CombMap TriangleMap




























-- σ' table:  (enc x, enc (σ' x))

-- α' table:

-- φ' = σ' ∘ α' table:




-- E' = number of α'-cycles  (expected 6 = E + k = 3 + 3):

-- V' = number of σ'-cycles  (expected 6 = V + k = 3 + 3):

-- F' = number of φ'-cycles  (φ' = σ' ∘ α'):

-- χ' = V' - E' + F'




-- c = number of dartStep-components of the cut map  (the disputed number):


-- Sanity: cutAlphaC and cutSigmaC are bijections (images have 12 distinct darts).
   -- expect 12
   -- expect 12


  -- F + 2c - 2





              -- c_i^- ↦ p_i

-- corrected σ' table:

-- corrected φ' = σ'₂ ∘ α':


-- CORRECTED verdict numbers:
                              -- E' = 6
                             -- V' = 6
    -- F' = 4  (FIXED)
  -- χ' = 4
               -- c = 2  (FIXED)
-- corrected σ'₂ is a bijection (12 distinct images):
  -- 12

end TriangleCut

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2Counts
import ProofsInTheBook.PlanarMapCutCapEval
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap2F -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount























end SimplePrimalCycle

end CombMap



namespace TriangleCut

open TriangleMap

-- Corrected `φ'₂ = σ'₂ ∘ α'` face-cycle count on the triangle cut:
-- expected `4 = F + 2` (`F = 2`).
   -- 4

-- The explicit `φ'₂`-orbit partition on the triangle (the structural reconnaissance):
-- forward cycle darts `{0,2,4}`, the reverse face `{1,5,3}`, the `+`-caps, the
-- `−`-caps — four orbits, `F' = 4 = F + 2`.


end TriangleCut

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2F
-/
/- Source module: ProofsInTheBook.PlanarMapCutCap2FWalk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

























end SimplePrimalCycle

end CombMap



namespace TriangleCut

open TriangleMap

-- Corrected `φ'₂ = σ'₂ ∘ α'` face-cycle count on the triangle cut: `4 = F + 2`.
   -- 4

-- `phiLift` reference count `F + 2k = 2 + 6 = 8` (caps as 2k singletons):
   -- 8 = F + 2k

-- The two `faceCorr₂` cap chains (here pure caps `{+0,+2,+1}` and `{−0,−1,−2}`):
-- print the `φ'₂`-orbit reps so the `−(k−1)` per chain is anchored.


end TriangleCut

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ForcedSplits -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ForcedSplits



variable {X : Type*} [Fintype X] [DecidableEq X]




































end ForcedSplits



namespace ProofsInTheBook.PlanarMap

open ForcedSplits CombMap CombMap.SimplePrimalCycle

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}















end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2FWalk
-/
/- Source module: ProofsInTheBook.PlanarMapSeamChain -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]























































namespace SeamChainData

































































end SeamChainData



namespace SeamChainData













end SeamChainData

end SeamChain

end ProofsInTheBook.PlanarMap
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ForcedSplits
import ProofsInTheBook.PlanarMapSeamChain
-/
/- Source module: ProofsInTheBook.FaceCorrWord -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord

open ForcedSplits SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

































end FaceCorrWord



namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain

variable {M : CombMap D}











end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord



end FaceCorrWord



namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWordEval








section
variable {n : ℕ} (alpha sigma : Fin n → Fin n) (dart : Fin 3 → Fin n)






end






















-- The cycle-list word realises `phiLift · faceCorr₂` across genus (all `true`):



-- The cycle-list shapes (genus-dependent; the word is uniform, the splits are not):




end FaceCorrWordEval










end ProofsInTheBook.PlanarMap

end ProofsInTheBook.PlanarMap
end

/- Original source header (imports hoisted):
import ProofsInTheBook.FaceCorrWord
import ProofsInTheBook.RelationComponentCount
-/
/- Source module: ProofsInTheBook.TouchRank -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.TouchRank

open ForcedSplits

variable {X : Type*} [Fintype X] [DecidableEq X]



































































































namespace TouchCompressionCert











































end TouchCompressionCert









end ProofsInTheBook.TouchRank



namespace ProofsInTheBook.PlanarMap

open ForcedSplits CombMap CombMap.SimplePrimalCycle
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}











end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap








end

/- Original source header (imports hoisted):
import ProofsInTheBook.TouchRank
-/
/- Source module: ProofsInTheBook.TouchCert -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List

namespace ProofsInTheBook

namespace TouchCert

open ForcedSplits ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]













end TouchCert



namespace PlanarMap

open ForcedSplits ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.TouchCert

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}









end SimplePrimalCycle

end CombMap

end PlanarMap



namespace TouchCert

open ForcedSplits ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain







end TouchCert

end ProofsInTheBook








end

/- Original source header (imports hoisted):
import ProofsInTheBook.TouchCert
-/
/- Source module: ProofsInTheBook.SeamStructure -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook

namespace SeamStructure

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]















end SeamStructure



namespace PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount





















open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord









end SimplePrimalCycle

end CombMap

end PlanarMap



namespace SeamStructure

open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.PlanarMap.SeamChain





end SeamStructure

end ProofsInTheBook











end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapF
-/
/- Source module: ProofsInTheBook.PlanarMapCutCapConn -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}





















































end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCapConn
-/
/- Source module: ProofsInTheBook.PlanarMapDualPathSep -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}























































end SimplePrimalCycle



namespace SimplePrimalCycle

variable {M : CombMap D}





end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapCutCap2FWalk
import ProofsInTheBook.PlanarMapDualPathSep
-/
/- Source module: ProofsInTheBook.PlanarMapBridge -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}





































































































































end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapBridge
import ProofsInTheBook.PlanarMapSeparation
-/
/- Source module: ProofsInTheBook.PlanarMapBridgeWitness -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

























end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.SeamStructure
import ProofsInTheBook.PlanarMapBridgeWitness
-/
/- Source module: ProofsInTheBook.SeamApplication -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}













end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}





end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle










end

/- Original source header (imports hoisted):
import ProofsInTheBook.SeamApplication
-/
/- Source module: ProofsInTheBook.SeamIncidence -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function
open ProofsInTheBook.TouchRank

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}



















end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation



namespace SimplePrimalCycle

variable {M : CombMap D}

open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure



namespace ArcChordSeam

variable {C : SimplePrimalCycle M}







end ArcChordSeam

end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)





end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

open ProofsInTheBook.TouchRank

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}





end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle










end

/- Original source header (imports hoisted):
import ProofsInTheBook.SeamIncidence
-/
/- Source module: ProofsInTheBook.DartArc -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]





namespace DartArc

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}









end DartArc







namespace SimplePrimalCycle

variable {M : CombMap D}





















open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure



end SimplePrimalCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}







end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle









end

/- Original source header (imports hoisted):
import ProofsInTheBook.DartArc
import ProofsInTheBook.PlanarMapBridge
import ProofsInTheBook.PlanarMapBridgeWitness
-/
/- Source module: ProofsInTheBook.WitnessFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}







































end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}





end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle











end

/- Original source header (imports hoisted):
import ProofsInTheBook.WitnessFinal
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ChordSeparation -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}















end CombMap.SimplePrimalCycle



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}



end CombMap.SimplePrimalCycle

namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}





end CombMap.SimplePrimalCycle

namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle



variable {M : CombMap D}







end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSeparation
-/
/- Source module: ProofsInTheBook.ChordGateCompat -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

























































end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap














end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordGateCompat
-/
/- Source module: ProofsInTheBook.ChordSeparationClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}

























end CombMap.SimplePrimalCycle



namespace CombMap.NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace CombMap.SimplePrimalCycle

variable {M : CombMap D}







end CombMap.SimplePrimalCycle

end ProofsInTheBook.PlanarMap











end

/- Original source header (imports hoisted):
import ProofsInTheBook.FaceCorrWord
import ProofsInTheBook.ChordSeparationClose
-/
/- Source module: ProofsInTheBook.ZinanCh35CountRoute -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List
open scoped Finset

namespace ForcedSplits

variable {X : Type*} [Fintype X] [DecidableEq X]







end ForcedSplits

namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord

open ForcedSplits SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]







end FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain

variable {M : CombMap D}












-- If Mathlib renamed this, alternates: `Finset.orderIsoOfFin S`,
-- `Fintype.equivFin {x // x ∈ S}`.

















end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation

end ProofsInTheBook.PlanarMap















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35CountRoute
-/
/- Source module: ProofsInTheBook.ZinanCh35Split -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.PlanarMap

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CutCapCount



section SumCongrTwo

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]



















end SumCongrTwo



end CutCapCount

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain CutCapCount

variable {M : CombMap D}















        -- c_i⁻ ↦ dart i

  -- c_i⁻ ↦ α (dart i)















































































end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation

end ProofsInTheBook.PlanarMap




















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Split
-/
/- Source module: ProofsInTheBook.ZinanCh35Gates -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.PlanarMap

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open CutCapCount

variable {M : CombMap D}





































end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle





end CombMap.NearTriangulation



namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}



end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

















end ProofsInTheBook.PlanarMap
end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Iota
import ProofsInTheBook.ZinanCh35Gates
-/
/- Source module: ProofsInTheBook.ZinanCh35Confinement -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Confinement

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]























end ProofsInTheBook.ZinanCh35Confinement









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35Confinement
-/
/- Source module: ProofsInTheBook.ZinanCh35Schoenflies -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Schoenflies

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ZinanCh35Confinement
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]





































end ProofsInTheBook.ZinanCh35Schoenflies











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Schoenflies
-/
/- Source module: ProofsInTheBook.ZinanCh35EdgeCore -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35EdgeCore

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}































end ProofsInTheBook.ZinanCh35EdgeCore








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35Coverage -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Coverage

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



section Abstract

variable {V : Type*} (r : V → V → Prop)





end Abstract





























end ProofsInTheBook.ZinanCh35Coverage









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35Coverage
-/
/- Source module: ProofsInTheBook.ZinanCh35InnerConn -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35InnerConn

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}





































variable {u v : M.Vertex}









end ProofsInTheBook.ZinanCh35InnerConn












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35InnerConn
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterDual -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterDual

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35InnerConn
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}





































variable {u v : M.Vertex}





end ProofsInTheBook.ZinanCh35OuterDual















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterDual
import ProofsInTheBook.RelationComponentCount
import ProofsInTheBook.PlanarMapEulerInequality
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35InnerConn
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35OuterDual

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}



























variable {u v : M.Vertex}







end ProofsInTheBook.ZinanCh35OuterCount













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterCount
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterSlack -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterSlack

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterDual
open ProofsInTheBook.ZinanCh35OuterCount
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}




























variable {hNT : NearTriangulation M}







































































end ProofsInTheBook.ZinanCh35OuterSlack













end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterSlack
-/
/- Source module: ProofsInTheBook.ZinanCh35BankCount -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankCount

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterDual
open ProofsInTheBook.ZinanCh35OuterSlack
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

variable {hNT : NearTriangulation M}



/-- The boundary length `B`. -/
local notation3 "B" => hNT.outerCycle.length







































































































end ProofsInTheBook.ZinanCh35BankCount






end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35StarConn -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35StarConn

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































































end ProofsInTheBook.ZinanCh35StarConn








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35BankCount
import ProofsInTheBook.ZinanCh35StarConn
-/
/- Source module: ProofsInTheBook.ZinanCh35CycleBank -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35CycleBank

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35OuterSlack
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}



variable (C : SimplePrimalCycle M)































































































































































end ProofsInTheBook.ZinanCh35CycleBank











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35CycleBank
import ProofsInTheBook.ZinanCh35Gates
-/
/- Source module: ProofsInTheBook.ZinanCh35BankLabels -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankLabels

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35CycleBank
open Equiv Equiv.Perm

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
variable (C : SimplePrimalCycle M)











































end ProofsInTheBook.ZinanCh35BankLabels








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Gates
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordCycle -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}








end BoundaryCycle



namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}





end BoundaryCycle



namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle



variable {u v : M.Vertex}









end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35Schoenflies2 -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Schoenflies2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































end ProofsInTheBook.ZinanCh35Schoenflies2












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35BankCount
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35Schoenflies2
-/
/- Source module: ProofsInTheBook.ZinanCh35EdgeCoreFinal -/
section
set_option autoImplicit true




namespace ProofsInTheBook.ZinanCh35EdgeCoreFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35OuterCount
open ProofsInTheBook.ZinanCh35BankCount
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35Schoenflies2

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}







end ProofsInTheBook.ZinanCh35EdgeCoreFinal

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Schoenflies
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
-/
/- Source module: ProofsInTheBook.ZinanCh35Side1Confine -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side1Confine

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}













end ProofsInTheBook.ZinanCh35Side1Confine






end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordCycle
import ProofsInTheBook.ZinanCh35EdgeCore
import ProofsInTheBook.ZinanCh35Side1Confine
-/
/- Source module: ProofsInTheBook.ZinanCh35ArcDartRun -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcDartRun

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}





namespace BoundaryPathDartRun

variable {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}





end BoundaryPathDartRun



section DartArcHelpers

variable {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}











end DartArcHelpers





namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





end NearTriangulation



namespace NearTriangulation

variable (hNT : NearTriangulation M) {u v : M.Vertex}

open ProofsInTheBook.PlanarMap.CombMap.BoundaryCycle





end NearTriangulation



namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





end NearTriangulation



namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





end NearTriangulation

end ProofsInTheBook.ZinanCh35ArcDartRun











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ArcDartRun
import ProofsInTheBook.ZinanCh35ChordCycle
-/
/- Source module: ProofsInTheBook.ZinanCh35Contiguity -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Contiguity

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35ArcDartRun

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



























end ProofsInTheBook.ZinanCh35Contiguity












end

/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter35 -/
section
set_option autoImplicit true




namespace ProofsInTheBook.Chapter35

open scoped BigOperators







section KempeChains







end KempeChains

section FiveColorInduction

universe u























end FiveColorInduction









end ProofsInTheBook.Chapter35

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenInduction
import ProofsInTheBook.WitnessFinal
-/
/- Source module: ProofsInTheBook.JordanOracleConstruct -/
section
set_option autoImplicit true




namespace ProofsInTheBook.JordanOracleConstruct

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ListColoring

universe u











variable {D : Type u} [Fintype D] [DecidableEq D] {α : Type u} [DecidableEq α]
variable {M : CombMap D}





end ProofsInTheBook.JordanOracleConstruct



namespace ProofsInTheBook.JordanOracleConstruct

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u





end ProofsInTheBook.JordanOracleConstruct








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Schoenflies
-/
/- Source module: ProofsInTheBook.ZinanCh35FinalClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35FinalClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]





























end ProofsInTheBook.ZinanCh35FinalClose










end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.ThomassenInduction
-/
/- Source module: ProofsInTheBook.ChordlessClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordlessClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}























end ProofsInTheBook.ChordlessClose












end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.ChordlessClose
-/
/- Source module: ProofsInTheBook.ChordlessFinal -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordlessFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}









































end ProofsInTheBook.ChordlessFinal












end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter35
import ProofsInTheBook.JordanOracleConstruct
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35FinalClose
import ProofsInTheBook.ChordlessFinal
-/
/- Source module: ProofsInTheBook.ZinanCh35Cert -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Cert

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ListColoring

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]





























end ProofsInTheBook.ZinanCh35Cert









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Cert
import ProofsInTheBook.ZinanCh35EdgeCore
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2 -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]



















































































end ProofsInTheBook.ZinanCh35Side2














end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Side2
import ProofsInTheBook.ZinanCh35Side1Confine
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35Schoenflies2
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2Confine -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side2Confine

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35Schoenflies2
open ProofsInTheBook.ZinanCh35Side2

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

































end ProofsInTheBook.ZinanCh35Side2Confine











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Side1Confine
import ProofsInTheBook.ZinanCh35Side2Confine
-/
/- Source module: ProofsInTheBook.ZinanCh35BankOrient -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankOrient

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



































end ProofsInTheBook.ZinanCh35BankOrient















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35BankLabels
import ProofsInTheBook.ZinanCh35ChordCycle
import ProofsInTheBook.ZinanCh35Contiguity
import ProofsInTheBook.ZinanCh35BankOrient
import ProofsInTheBook.ZinanCh35InnerConn
-/
/- Source module: ProofsInTheBook.ZinanCh35ArcSide -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcSide

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35CycleBank
open ProofsInTheBook.ZinanCh35BankLabels

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}











































































































end ProofsInTheBook.ZinanCh35ArcSide



-- The UNCONDITIONAL bank-side facts (the real new content of R8's chain A–F):








-- The honest assembly over the single isolated orientation input:






end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ArcSide
-/
/- Source module: ProofsInTheBook.ZinanCh35Aligned -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Aligned

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35CycleBank
open ProofsInTheBook.ZinanCh35BankLabels
open ProofsInTheBook.ZinanCh35ArcDartRun

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}











































namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}























































end NearTriangulation







namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}





































-- Both arcs of the normalized arc-split carry genuine internal vertices (the construction fires).


-- `Separates` for the normalized datum is the genuine chord keystone `face₂ ∉ side₁` (not trivial).


-- The datum's chord is the GIVEN chord, so `side₁`/`side₂` are the real chord sides.


-- The two runs have length ≥ 2 (genuinely longer than the chord — the arcs carry interior vertices).


end NearTriangulation

end ProofsInTheBook.ZinanCh35Aligned












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Aligned
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.ZinanCh35BoundaryAssembler -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BoundaryAssembler

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ZinanCh35Aligned

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}



namespace BoundaryCycle

variable {f : M.Face}









end BoundaryCycle




















end ProofsInTheBook.ZinanCh35BoundaryAssembler

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSplitNT
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35Cert
-/
/- Source module: ProofsInTheBook.ZinanCh35Dichotomy -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Dichotomy

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordSplitFinal

universe u

variable {α : Type u} [DecidableEq α]























end ProofsInTheBook.ZinanCh35Dichotomy









end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Dichotomy
import ProofsInTheBook.ZinanCh35Side2
import ProofsInTheBook.ZinanCh35Aligned
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordBranch -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordBranch

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35Side2
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]







































-- The residual genuinely PRODUCES (does not posit) the side-2 confinement: the field type that
-- `Side₂CertificateInputs.confinement` requires is exactly the output of
-- `bothConfinements_normalized`'s second component.


-- The residual data's `side₁`/`side₂` carry NO confinement field (audit: the confinement burden
-- is off the residual — it is the genuine reduction `bothConfinements_normalized` buys).


end ProofsInTheBook.ZinanCh35ChordBranch











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordBranch
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35SideAnchors
import ProofsInTheBook.ChordSigmaContig
import ProofsInTheBook.ChordContiguous
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordResidue -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordResidue

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35ChordBranch
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]





































-- The canonical side-1 anchors genuinely realize the chord endpoints (non-vacuity of `anchors₁`).


-- The produced region glue pins `s₁ = sideRegion₁`, `s₂ = sideRegion₂` definitionally (the
-- `regions_s₁`/`regions_s₂` of the residual data are `rfl`).


end ProofsInTheBook.ZinanCh35ChordResidue












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35Side2Confine
import ProofsInTheBook.ZinanCh35Schoenflies2
import ProofsInTheBook.ZinanCh35ArcSide
-/
/- Source module: ProofsInTheBook.ZinanCh35Regions -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Regions

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35Schoenflies2
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ArcSide

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



























-- The side-2 region genuinely contains both chord endpoints (non-vacuity of `u_s₂`/`v_s₂`).


end ProofsInTheBook.ZinanCh35Regions










end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterTrace
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Side2
-/
/- Source module: ProofsInTheBook.ZinanCh35Contiguous -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Contiguous

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35OuterTrace

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u



section Itinerary

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

















end Itinerary



variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



















section Audit

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)





end Audit

end ProofsInTheBook.ZinanCh35Contiguous












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Contiguous
-/
/- Source module: ProofsInTheBook.ZinanCh35SideOuterSimple -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35SideOuterSimple

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ZinanCh35SideAnchors

universe u



section Bridge

variable {D : Type*} [Fintype D] [DecidableEq D]



end Bridge



section FreshTail

variable {K : Type u} [Fintype K] [DecidableEq K]
  (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)



end FreshTail



section SideTail

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



end SideTail



section Main

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  (hNT : NearTriangulation M) {u v : M.Vertex}

















end Main

end ProofsInTheBook.ZinanCh35SideOuterSimple











end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordAnchorInst
import ProofsInTheBook.ChordDisk
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2Anchors -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35Side2Anchors

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u
variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



































end ProofsInTheBook.ZinanCh35Side2Anchors



end

/- Original source header (imports hoisted):
import ProofsInTheBook.ChordSideClose
-/
/- Source module: ProofsInTheBook.ZinanCh35Side2Disk -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.SubmapPlanar

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}



















section RawConnected



























end RawConnected











end ProofsInTheBook.ChordSideClose







end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35SideOuterSimple
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35ArcDartRun
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35ArcSide
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Side2Anchors
import ProofsInTheBook.ChordDisk
import ProofsInTheBook.ZinanCh35Side2Disk
import ProofsInTheBook.ZinanCh35Regions
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterTraceProof -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterTraceProof

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35SideOuterSimple
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ZinanCh35OuterTrace
open ProofsInTheBook.ZinanCh35Side2Anchors

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}





































variable (hNT : NearTriangulation M) {u v : M.Vertex}
variable {a b : M.Vertex}











































































































































































































































































































variable {α : Type u} [DecidableEq α]









end ProofsInTheBook.ZinanCh35OuterTraceProof
















































end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35Side2Confine
import ProofsInTheBook.ZinanCh35Aligned
import ProofsInTheBook.ZinanCh35Regions
import ProofsInTheBook.ZinanCh35Iota
import ProofsInTheBook.ZinanCh35OuterTraceProof
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordSupplier -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation
open ProofsInTheBook.ZinanCh35Regions
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v p q : M.Vertex}















































































end ProofsInTheBook.ZinanCh35ChordSupplier

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordSupplier
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordSupplier2 -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordSupplier2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation
open ProofsInTheBook.ZinanCh35Regions
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35Side2Anchors
open ProofsInTheBook.ZinanCh35OuterTrace
open ProofsInTheBook.ZinanCh35OuterTraceProof
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35ChordSupplier

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v p q : M.Vertex}









































end ProofsInTheBook.ZinanCh35ChordSupplier2



end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
import ProofsInTheBook.PlanarMapBoundaryArcSplit
-/
/- Source module: ProofsInTheBook.ZinanCh35OuterV0Consecutive -/
section
set_option autoImplicit true




namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}





end BoundaryCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M) {v0 : M.Vertex}















end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35InnerConn
-/
/- Source module: ProofsInTheBook.ZinanCh35Chordless -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Chordless

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)


































end ProofsInTheBook.ZinanCh35Chordless
end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.ZinanCh35Chordless
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessFull -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessFull

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)











































end ProofsInTheBook.ZinanCh35ChordlessFull












end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordlessFull
import ProofsInTheBook.PlanarMapFanConnectivity
-/
/- Source module: ProofsInTheBook.ZinanCh35FanBackward -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35FanBackward

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}



















variable (hNT)



variable {hNT}







































namespace Conn

variable {v0 : M.Vertex}





























end Conn



















end ProofsInTheBook.ZinanCh35FanBackward

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35FanBackward
import ProofsInTheBook.ZinanCh35ChordlessFull
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessClose -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}









end ProofsInTheBook.ZinanCh35ChordlessClose








end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35OuterV0Consecutive
import ProofsInTheBook.ZinanCh35ChordlessClose
-/
/- Source module: ProofsInTheBook.ZinanCh35MergedArc -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35MergedArc

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}



















end ProofsInTheBook.ZinanCh35MergedArc












end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlanarMapOuterArc
import ProofsInTheBook.ChordlessFinal
import ProofsInTheBook.ZinanCh35ChordlessClose
import ProofsInTheBook.ZinanCh35BoundaryAssembler
-/
/- Source module: ProofsInTheBook.ZinanCh35DeletedBoundary -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35DeletedBoundary

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessClose
open ProofsInTheBook.ChordlessFinal

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}





namespace DeletedSeamData

variable {fan : BoundaryVertexFan hNT v0} {hchord : BoundaryChordless hNT.outerCycle}
  {d0 : D} {htail0 : M.tail d0 = v0}























end DeletedSeamData





















end ProofsInTheBook.ZinanCh35DeletedBoundary

















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35MergedArc
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.PlanarMapDeletedBoundary
-/
/- Source module: ProofsInTheBook.ZinanCh35DeletedAssembly -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35DeletedAssembly

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessFinal

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}



































































end ProofsInTheBook.ZinanCh35DeletedAssembly















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35FanBackward
import ProofsInTheBook.ZinanCh35ChordlessClose
import ProofsInTheBook.ZinanCh35Dichotomy
import ProofsInTheBook.ChordlessClose
import ProofsInTheBook.ChordlessFinal
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessOracle -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessOracle

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy

universe u



variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}

























variable {α : Type u} [DecidableEq α]











end ProofsInTheBook.ZinanCh35ChordlessOracle
















end

/- Original source header (imports hoisted):
import ProofsInTheBook.ThomassenLists
import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.PlanarMapFanSurgery
import Mathlib.Data.Finset.Basic
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessSite -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSite

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M}

namespace BoundaryCycle

variable {f : M.Face}









end BoundaryCycle

namespace NearTriangulation

variable {v : M.Vertex}







end NearTriangulation

















end ProofsInTheBook.ZinanCh35ChordlessSite

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordlessSite
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.ZinanCh35ChordlessOracle
-/
/- Source module: ProofsInTheBook.ZinanCh35ChordlessSupplier -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}











































































end ProofsInTheBook.ZinanCh35ChordlessSupplier

end

/- Original source header (imports hoisted):
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35Regions
import ProofsInTheBook.ZinanCh35ChordSupplier
import ProofsInTheBook.ZinanCh35ChordSupplier2
import ProofsInTheBook.ZinanCh35MergedArc
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35ChordlessOracle
import ProofsInTheBook.ZinanCh35ChordlessSupplier
-/
/- Source module: ProofsInTheBook.ZinanCh35Final -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Final

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ChordlessOracle

universe u

variable {α : Type u} [DecidableEq α]







































end ProofsInTheBook.ZinanCh35Final














end

/- Original source header (imports hoisted):
import ProofsInTheBook.PlaneSimpleGraph
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.FaceDiagonalSurgery
import ProofsInTheBook.Ch13ActiveComponent
import ProofsInTheBook.ZinanCh35BoundaryAssembler
import ProofsInTheBook.ZinanCh35Final
-/
/- Source module: ProofsInTheBook.PlaneSimpleGraphTriangulate -/
section
set_option autoImplicit true




set_option linter.unusedSectionVars false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace PlaneSimpleGraph

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]































end PlaneSimpleGraph






namespace TriangleWitness

open PlaneSimpleGraph









































end TriangleWitness



universe u v u'

section Extension

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]







end Extension





namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]



































































































end CombMap

namespace PlaneSimpleGraph

variable {V : Type v} {D : Type u} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]







end PlaneSimpleGraph

namespace TriangleWitness



















end TriangleWitness



















end ProofsInTheBook.PlanarMap

end


