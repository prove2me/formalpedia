-- Prove2me | Definitions.Def_AT260939824_RowValidity
-- name    : AT260939824_RowValidity
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:57:35.546991+00:00
-- url     : https://prove2.me/theorems/6479ade1-3938-4fe4-aad8-30e80f1c9e0b
-- title:
--   Validity of vertex rows in a downward-closed face system
-- statement:
--   Let $V$ be a vertex set with decidable equality, and let $\mathcal F$ be a predicate on finite subsets of $V$. Downward closure means $s\in\mathcal F$ and $t\subseteq s$ imply $t\in\mathcal F$. A finite row is valid if each of its vertices is a singleton face and every pair of consecutive vertices is a face:
--   $$[v_0,\ldots,v_n]\text{ valid}\ \Longleftrightarrow\
--   \{v_j\}\in\mathcal F\ \forall j,\quad\{v_j,v_{j+1}\}\in\mathcal F\ \forall j<n.$$
--   For downward-closed $\mathcal F$, insertion or deletion of a triangle's middle vertex preserves validity; repeated-vertex insertion or deletion also preserves it. Bounded triangle-row deformations therefore preserve validity. Word paths contained in an interval carrier give valid rows of its face system.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/RowValidity.lean, selected declaration lines 10-11, 13-15, 17-32, 34-53, 55-83, 85-108, 110-118, 120-124, 133-143, 147-155; SHA-256 d1abd6b7c10ef4a6ca835d36ac10a955c170263aad7039ff762b15200427446c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_PauseSliding
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_TriangleRowMoves
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! # Valid edge rows and preservation under the actual cellular moves -/

namespace AbelianTargets

variable {V : Type*} [DecidableEq V] {Face : Finset V → Prop}

def FaceDownward (Face : Finset V → Prop) : Prop :=
  ∀ ⦃s t : Finset V⦄, Face s → t ⊆ s → Face t

structure ValidRow (Face : Finset V → Prop) (w : List V) : Prop where
  chain : List.IsChain (fun a b => Face {a,b}) w
  vertices : ∀ a ∈ w, Face {a}

theorem face_pair_of_triangle (hd : FaceDownward Face) {a b c : V}
    (hf : Face {a,b,c}) : Face {a,b} ∧ Face {b,c} ∧ Face {a,c} := by
  constructor
  · apply hd hf
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
    obtain rfl | rfl := hv <;> simp
  · constructor
    · apply hd hf
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      obtain rfl | rfl := hv <;> simp
    · apply hd hf
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
      obtain rfl | rfl := hv <;> simp

theorem face_vertices_of_triangle (hd : FaceDownward Face) {a b c : V}
    (hf : Face {a,b,c}) : Face {a} ∧ Face {b} ∧ Face {c} := by
  have hp := face_pair_of_triangle hd hf
  constructor
  · apply hd hp.1
    intro v hv
    have hv' : v = a := Finset.mem_singleton.mp hv
    subst v
    simp
  · constructor
    · apply hd hp.1
      intro v hv
      have hv' : v = b := Finset.mem_singleton.mp hv
      subst v
      simp
    · apply hd hp.2.2
      intro v hv
      have hv' : v = c := Finset.mem_singleton.mp hv
      subst v
      simp

theorem validRow_triangle_iff (hd : FaceDownward Face) (a b c : V)
    (hf : Face {a,b,c}) (p s : List V) :
    ValidRow Face (p++[a,b,c]++s) ↔ ValidRow Face (p++[a,c]++s) := by
  obtain ⟨hab,hbc,hac⟩ := face_pair_of_triangle hd hf
  obtain ⟨ha,hb,hc⟩ := face_vertices_of_triangle hd hf
  have hchain : List.IsChain (fun a b => Face {a,b}) (p++[a,b,c]++s) ↔
      List.IsChain (fun a b => Face {a,b}) (p++[a,c]++s) := by
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.isChain_append_cons_cons,
      List.isChain_cons_cons,hab,hbc,hac,true_and,and_true]
  have hvert : (∀ v ∈ p++[a,b,c]++s, Face {v}) ↔
      (∀ v ∈ p++[a,c]++s, Face {v}) := by
    simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,or_assoc]
    constructor
    · intro h v hv
      apply h v
      obtain hv | rfl | rfl | hv := hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hv)))
    · intro h v hv
      obtain hv | rfl | rfl | rfl | hv := hv
      · exact h v (Or.inl hv)
      · exact ha
      · exact hb
      · exact hc
      · exact h v (Or.inr (Or.inr (Or.inr hv)))
  exact ⟨fun h => ⟨hchain.mp h.chain,hvert.mp h.vertices⟩,
    fun h => ⟨hchain.mpr h.chain,hvert.mpr h.vertices⟩⟩

theorem validRow_pause_iff (a : V) (p s : List V) :
    ValidRow Face (p++[a,a]++s) ↔ ValidRow Face (p++[a]++s) := by
  have hvert : (∀ v ∈ p++[a,a]++s, Face {v}) ↔
      (∀ v ∈ p++[a]++s, Face {v}) := by
    simp [List.forall_mem_append,and_assoc]
  constructor
  · intro h
    have ha : Face {a} := h.vertices a (by simp)
    have haa : Face {a,a} := by simpa using ha
    have hc := h.chain
    simp only [List.append_assoc,List.cons_append,List.nil_append,List.isChain_append_cons_cons,
      haa,true_and,and_true] at hc
    refine ⟨?_,hvert.mp h.vertices⟩
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using (List.isChain_split.mpr hc)
  · intro h
    have ha : Face {a} := h.vertices a (by simp)
    have haa : Face {a,a} := by simpa using ha
    constructor
    · have hc := h.chain
      simp only [List.append_assoc,List.cons_append,List.nil_append] at hc
      have hc' := List.isChain_split.mp hc
      simpa only [List.append_assoc,List.cons_append,List.nil_append,List.isChain_append_cons_cons,
        haa,true_and,and_true] using hc'
    · exact hvert.mpr h.vertices

theorem BoundedTriangleRows.valid_iff {B : ℕ} {w z : List V}
    (h : BoundedTriangleRows Face B w z) (hd : FaceDownward Face) :
    ValidRow Face w ↔ ValidRow Face z := by
  induction h with
  | refl w hl => rfl
  | triangle a b c hf p s hw hz => exact validRow_triangle_iff hd a b c hf p s
  | pause a p s hw hz => exact validRow_pause_iff a p s
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem EdgeRow.isChain {a z : V} {tail : List V} (h : EdgeRow Face a tail z) :
    List.IsChain (fun a b => Face {a,b}) (a::tail) := by
  induction h with
  | nil a => exact .singleton a
  | cons hf h ih => exact .cons_cons hf ih



theorem edgeRow_of_chain_last {a z : V} {tail : List V}
    (hc : List.IsChain (fun a b => Face {a,b}) (a::tail))
    (hz : (a::tail).getLast? = some z) : EdgeRow Face a tail z := by
  induction tail generalizing a with
  | nil =>
      have ha : a = z := Option.some.inj hz
      subst z
      exact .nil a
  | cons b tail ih =>
      have hpair := List.isChain_cons_cons.mp hc
      exact .cons hpair.1 (ih hpair.2 (by simpa only [List.getLast?_cons_cons] using hz))

namespace IntervalCarriers

theorem WordPath.validRow {m K : ℕ} {A B : ℤ} {x z : Vertex} {w : List BSLetter}
    (hm : 1 ≤ m) (p : WordPath m x w z)
    (hp : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B) :
    ValidRow (CarrierFace m K A B) p.vertices := by
  have hc := (p.edgeRow hm hp).isChain
  have hrow : p.vertices = x :: p.vertices.tail := by cases p <;> rfl
  refine ⟨by simpa only [← hrow] using hc,?_⟩
  intro v hv
  exact Or.inl ⟨v,hp v hv,Finset.Subset.refl _⟩

end IntervalCarriers

end AbelianTargets


