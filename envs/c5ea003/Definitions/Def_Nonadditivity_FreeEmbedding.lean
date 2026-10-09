-- Prove2me | Definitions.Def_Nonadditivity_FreeEmbedding
-- name    : Nonadditivity_FreeEmbedding
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:34:50.833768+00:00
-- url     : https://prove2.me/theorems/27331cae-b22c-4536-ad46-5e0cf27f00fb
-- title:
--   Free-generator word maps from a finite binary covering graph
-- statement:
--   Let $F_2=F(\{x,y\})$ be the two-generator free group. One word homomorphism sends generator $i$ of $F_K$ to $x^iyx^{-i}$. A second construction uses the labelled binary tree on $M>0$ vertices, with
--   $$\operatorname{child}(b,v)=2v+\begin{cases}2,&b=\mathrm{true},\\1,&b=\mathrm{false}.\end{cases}$$
--   Each partial child map is completed to a permutation of the vertices. Paths from the distinguished root turn non-tree edges into based loops; their cardinality is at least $M+1$. Selecting $M+1$ such edges defines a homomorphism $F_{M+1}\to F_2$. With $M=K-1$, the bundle defines the source's logarithmic-embedding word map $F_K\to F_2$ for $K\ge2$.
--   The imported declarations provide these concrete homomorphisms, vertex paths, edge predicates, cardinality bounds, and permutation completions. They supply the generator words used by the structured finite-representation construction.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/FreeEmbedding.lean#L30-L431

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/












/-!
# Explicit free subgroup of the free group on two generators

The binary covering graph construction proves the manuscript's short
embedding lemma, with generator length bound `2 * Nat.log 2 (K-1) + 1`.
A concrete finite state permutation representation proves injectivity,
without a topological covering-space hypothesis or an assumed free basis.
The file also includes the elementary conjugate construction `x^i y x^-i`
with length bound `2*K-1`.
-/

namespace Nonadditivity.FreeEmbedding

abbrev Two := FreeGroup Bool

def x : Two := FreeGroup.of false
def y : Two := FreeGroup.of true

/-- The `i`th conjugate in the explicit infinite free subgroup. -/
def conjugate (i : ℕ) : Two := x ^ i * y * (x ^ i)⁻¹



















/-- The actual homomorphism sending generator `i` to `x^i y x^-i`. -/
def embedding (K : ℕ) : FreeGroup (Fin K) →* Two :=
  FreeGroup.lift (fun i => conjugate i.val)

@[simp] theorem embedding_of (K : ℕ) (i : Fin K) :
    embedding K (FreeGroup.of i) = conjugate i.val := by
  simp [embedding]









end Nonadditivity.FreeEmbedding

namespace Nonadditivity.FreeEmbedding.Covering

 def child (b : Bool) (v : ℕ) : ℕ := 2 * v + if b then 2 else 1

 theorem child_pos (b : Bool) (v : ℕ) : 0 < Nonadditivity.FreeEmbedding.Covering.child b v := by
  cases b <;> simp [Nonadditivity.FreeEmbedding.Covering.child]

 theorem child_injective (b : Bool) : Function.Injective (Nonadditivity.FreeEmbedding.Covering.child b) := by
  intro v w h
  cases b <;> simp [Nonadditivity.FreeEmbedding.Covering.child] at h <;> omega

 theorem child_pair_injective {b c : Bool} {v w : ℕ}
    (h : Nonadditivity.FreeEmbedding.Covering.child b v = Nonadditivity.FreeEmbedding.Covering.child c w) : b = c ∧ v = w := by
  cases b <;> cases c <;> simp [Nonadditivity.FreeEmbedding.Covering.child] at h ⊢ <;> omega

 def treeEdge (M : ℕ) (e : Bool × Fin M) : Prop := Nonadditivity.FreeEmbedding.Covering.child e.1 e.2.val < M

 instance treeEdgeDecidable (M : ℕ) : DecidablePred (Nonadditivity.FreeEmbedding.Covering.treeEdge M) :=
  fun e => inferInstanceAs (Decidable (Nonadditivity.FreeEmbedding.Covering.child e.1 e.2.val < M))

 abbrev TreeEdges (M : ℕ) := {e : Bool × Fin M // Nonadditivity.FreeEmbedding.Covering.treeEdge M e}
 abbrev ExtraEdges (M : ℕ) := {e : Bool × Fin M // ¬ Nonadditivity.FreeEmbedding.Covering.treeEdge M e}

 def partialTarget (M : ℕ) (b : Bool) :
    {v : Fin M // Nonadditivity.FreeEmbedding.Covering.child b v.val < M} → Fin M :=
  fun v => ⟨Nonadditivity.FreeEmbedding.Covering.child b v.val, v.property⟩

 theorem partialTarget_injective (M : ℕ) (b : Bool) :
    Function.Injective (Nonadditivity.FreeEmbedding.Covering.partialTarget M b) := by
  intro v w h
  apply Subtype.ext
  apply Fin.ext
  apply Nonadditivity.FreeEmbedding.Covering.child_injective b
  exact congrArg Fin.val h

/-- Each partial labelled binary-tree map is completed to an actual permutation. -/
 noncomputable def transition (M : ℕ) (b : Bool) : Equiv.Perm (Fin M) :=
  (Equiv.ofInjective (Nonadditivity.FreeEmbedding.Covering.partialTarget M b) (Nonadditivity.FreeEmbedding.Covering.partialTarget_injective M b)).extendSubtype















 def parent (v : ℕ) : ℕ := (v - 1) / 2
 def parentLabel (v : ℕ) : Bool := decide (v % 2 = 0)

 theorem parent_lt {v : ℕ} (h : 0 < v) : Nonadditivity.FreeEmbedding.Covering.parent v < v := by
  unfold Nonadditivity.FreeEmbedding.Covering.parent
  omega



 def path (v : ℕ) : Two :=
  if v = 0 then 1 else FreeGroup.of (Nonadditivity.FreeEmbedding.Covering.parentLabel v) * path (Nonadditivity.FreeEmbedding.Covering.parent v)
termination_by v
decreasing_by apply Nonadditivity.FreeEmbedding.Covering.parent_lt; omega











 noncomputable def basedLoop (M : ℕ) (e : Nonadditivity.FreeEmbedding.Covering.ExtraEdges M) : Two :=
  (Nonadditivity.FreeEmbedding.Covering.path (Nonadditivity.FreeEmbedding.Covering.transition M e.val.1 e.val.2).val)⁻¹ *
    FreeGroup.of e.val.1 * Nonadditivity.FreeEmbedding.Covering.path e.val.2.val



 noncomputable def loopMap (M : ℕ) : FreeGroup (Nonadditivity.FreeEmbedding.Covering.ExtraEdges M) →* Two :=
  FreeGroup.lift (Nonadditivity.FreeEmbedding.Covering.basedLoop M)







 def treeTarget (M : ℕ) (hM : 0 < M) :
    Nonadditivity.FreeEmbedding.Covering.TreeEdges M → {v : Fin M // v ≠ ⟨0, hM⟩} := fun e =>
  ⟨⟨Nonadditivity.FreeEmbedding.Covering.child e.val.1 e.val.2.val, e.property⟩, by
    intro h
    have hv := congrArg Fin.val h
    have hp := Nonadditivity.FreeEmbedding.Covering.child_pos e.val.1 e.val.2.val
    change Nonadditivity.FreeEmbedding.Covering.child e.val.1 e.val.2.val = 0 at hv
    omega⟩

 theorem treeTarget_injective (M : ℕ) (hM : 0 < M) :
    Function.Injective (Nonadditivity.FreeEmbedding.Covering.treeTarget M hM) := by
  intro e f hef
  have hchild : Nonadditivity.FreeEmbedding.Covering.child e.val.1 e.val.2.val = Nonadditivity.FreeEmbedding.Covering.child f.val.1 f.val.2.val :=
    congrArg (fun z => z.val.val) hef
  obtain ⟨hb, hv⟩ := Nonadditivity.FreeEmbedding.Covering.child_pair_injective hchild
  apply Subtype.ext
  exact Prod.ext hb (Fin.ext hv)

 theorem extraEdges_card (M : ℕ) (hM : 0 < M) :
    M + 1 ≤ Fintype.card (Nonadditivity.FreeEmbedding.Covering.ExtraEdges M) := by
  classical
  have htree := Fintype.card_le_of_injective (Nonadditivity.FreeEmbedding.Covering.treeTarget M hM) (Nonadditivity.FreeEmbedding.Covering.treeTarget_injective M hM)
  have hnonroot : Fintype.card {v : Fin M // v ≠ ⟨0, hM⟩} = M - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hnonroot] at htree
  have hcomp : Fintype.card (Nonadditivity.FreeEmbedding.Covering.ExtraEdges M) = 2 * M - Fintype.card (Nonadditivity.FreeEmbedding.Covering.TreeEdges M) := by
    rw [Fintype.card_subtype_compl]
    simp
  omega

 noncomputable def edgeIndex (M : ℕ) (hM : 0 < M) : Fin (M + 1) ↪ Nonadditivity.FreeEmbedding.Covering.ExtraEdges M :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa using Nonadditivity.FreeEmbedding.Covering.extraEdges_card M hM))

/-- The binary covering graph gives `M+1` independent based loops in `F₂`. -/
noncomputable def shortEmbedding (M : ℕ) (hM : 0 < M) : FreeGroup (Fin (M + 1)) →* Two :=
  (Nonadditivity.FreeEmbedding.Covering.loopMap M).comp (FreeGroup.map (Nonadditivity.FreeEmbedding.Covering.edgeIndex M hM))





end Nonadditivity.FreeEmbedding.Covering

namespace Nonadditivity.FreeEmbedding

/-- The manuscript's embedding, obtained by completing the labelled binary
tree on `K-1` vertices and selecting `K` of its non-tree based loops. -/
noncomputable def logarithmicEmbedding (K : ℕ) (hK : 2 ≤ K) :
    FreeGroup (Fin K) →* Two :=
  (Covering.shortEmbedding (K - 1) (by omega)).comp
    (FreeGroup.freeGroupCongr (finCongr (by omega : K = K - 1 + 1))).toMonoidHom







end Nonadditivity.FreeEmbedding


