-- Prove2me | Definitions.Def_AT260939824_PresentationPathRows
-- name    : AT260939824_PresentationPathRows
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:56:06.708604+00:00
-- url     : https://prove2.me/theorems/cbd56879-3e24-45ee-857b-fb2816d81315
-- title:
--   Row homotopies for presentation relations
-- statement:
--   In a finite carrier for a base $m\ge2$, the literal path labelled by $tat^{-1}$ and the path labelled by $a^m$ along one presentation polygon are connected by a bounded triangle-row chain with budget $m+2$. A two-edge directed backtrack contracts through its edge face and a pause deletion with budget three. The certificates retain the actual endpoint and vertex lists.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/PresentationPathRows.lean, selected declaration lines 7-12, 14-19, 21-38, 40-62, 64-81, 83-91, 93-122; SHA-256 482c779cfbb33fa96d1ce4eda0214714773442659f7bed0f89139d647e40f67d. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_BoundedCarries
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_TriangleRowMoves
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! # Edge-labelled sides of the actual presentation polygon -/

namespace AbelianTargets.IntervalCarriers

theorem lowerVertex_comp (m : ℕ) (c : Vertex) (l n : ℕ) :
    lowerVertex m (lowerVertex m c.1 c.2 l).1 (lowerVertex m c.1 c.2 l).2 n =
      lowerVertex m c.1 c.2 (l+n) := by
  simp only [lowerVertex,Nat.cast_add]
  congr 1
  ring

theorem lowerRow_shift (m : ℕ) (c : Vertex) (l n k : ℕ) :
    lowerRow m (lowerVertex m c.1 c.2 l) n k = lowerRow m c (l+n) k := by
  induction k generalizing n with
  | zero => simp only [lowerRow,lowerVertex_comp]
  | succ k ih =>
      simp only [lowerRow,lowerVertex_comp,ih,Nat.add_assoc]

theorem WordPath.aWord_vertices {m n : ℕ} {c z : Vertex}
    (p : WordPath m c (aWord n) z) : p.vertices = lowerRow m c 0 n := by
  induction n generalizing c with
  | zero => cases p; cases z; simp [WordPath.vertices,lowerRow,lowerVertex]
  | succ n ih =>
      have hword : aWord (n+1) = BSLetter.a :: aWord n := by
        simp only [aWord,List.replicate_succ]
      let p' := p.castWord hword
      have hp : p'.vertices = p.vertices := p.vertices_castWord hword
      rw [← hp]
      cases p' with
      | @cons s c y z w h q =>
        have hy : y = lowerVertex m c.1 c.2 1 := by
          simpa only [LetterStep,HorizontalStep,lowerVertex,Nat.cast_one,one_mul] using h
        have hq := ih q
        simp only [WordPath.vertices,hq,hy,lowerRow_shift,zero_add,lowerRow]
        have hc : lowerVertex m c.1 c.2 0 = c := by cases c; simp [lowerVertex]
        rw [hc]

theorem WordPath.relation_endpoint {m : ℕ} {c z : Vertex}
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z) :
    z = lowerVertex m c.1 c.2 m := by
  cases p with
  | cons ht p =>
    cases p with
    | cons ha p =>
      cases p with
      | cons hd p =>
        cases p
        have ht' := ht
        have ha' := ha
        have hd' := hd
        simp only [LetterStep,VerticalStep,HorizontalStep] at ht' ha' hd'
        rw [ht'] at ha'
        rw [ha'] at hd'
        have hx := congrArg Prod.fst hd'
        have hj := congrArg Prod.snd hd'
        apply Prod.ext
        · simp only [lowerVertex,pow_succ] at hx ⊢
          simpa only [mul_comm] using hx.symm
        · simp only [lowerVertex] at hj ⊢
          omega

theorem WordPath.relation_vertices {m : ℕ} {c z : Vertex}
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z) :
    p.vertices = [lowerVertex m c.1 c.2 0,upperLeft c.1 c.2,
      upperRight m c.1 c.2,lowerVertex m c.1 c.2 m] := by
  have hz := p.relation_endpoint
  cases p with
  | cons ht p =>
    cases p with
    | cons ha p =>
      cases p with
      | cons hd p =>
        cases p
        simp only [LetterStep,VerticalStep,HorizontalStep] at ht ha
        rw [ht] at ha
        simp only [WordPath.vertices,ht,ha,hz]
        have hc : lowerVertex m c.1 c.2 0 = c := by cases c; simp [lowerVertex]
        rw [hc]
        rfl

/-- Exact labelled relation sides inherit the bounded fan row
homotopy, including their literal vertex lists. -/
theorem presentation_path_rows {m K : ℕ} {A B : ℤ} {c z z' : Vertex}
    (hm : 2 ≤ m) (hc : c ∈ carrierCells m K A B)
    (p : WordPath m c [BSLetter.t,BSLetter.a,BSLetter.tInv] z)
    (q : WordPath m c (aWord m) z') :
    BoundedTriangleRows (CarrierFace m K A B) (m+2) q.vertices p.vertices := by
  rw [q.aWord_vertices,p.relation_vertices]
  exact presentation_polygon_rows hm hc

/-- Every actual two-edge backtrack contracts through its edge face
and one pause deletion, using at most three vertex entries. -/
theorem WordPath.two_edge_spur_rows {m K : ℕ} {A B : ℤ} {c : Vertex} {s t : BSLetter}
    (hm : 1 ≤ m) (p : WordPath m c [s,t] c)
    (hvertices : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B) :
    BoundedTriangleRows (CarrierFace m K A B) 3 p.vertices [c] := by
  cases p with
  | @cons s c y c w h p =>
    cases p with
    | cons h' p =>
      cases p
      have hc : c ∈ carrierVertices K A B := hvertices c (by simp [WordPath.vertices])
      have hy : y ∈ carrierVertices K A B := hvertices y (by simp [WordPath.vertices])
      have hf : CarrierFace m K A B {c,y,c} := by
        apply Or.inr
        apply Or.inl
        refine ⟨c,hc,y,hy,h.adj hm,?_⟩
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv ⊢
        obtain rfl | rfl | rfl := hv
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
      have h₁ : BoundedTriangleRows (CarrierFace m K A B) 3 [c,y,c] [c,c] := by
        simpa only [List.nil_append,List.append_nil] using
          BoundedTriangleRows.triangle c y c hf [] [] (by simp) (by simp)
      have h₂ : BoundedTriangleRows (CarrierFace m K A B) 3 [c,c] [c] := by
        simpa only [List.nil_append,List.append_nil] using
          BoundedTriangleRows.pause (Face := CarrierFace m K A B) c [] [] (by simp) (by simp)
      exact h₁.trans h₂

end AbelianTargets.IntervalCarriers


