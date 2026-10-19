-- Prove2me | Definitions.Def_AT260939824_PauseSliding
-- name    : AT260939824_PauseSliding
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:56:44.354969+00:00
-- url     : https://prove2.me/theorems/e25de2ba-8481-4678-92d4-a947123da666
-- title:
--   Fixed-slot row moves and pause transport
-- statement:
--   For an admissible-face predicate on a vertex set, fixed-row moves replace a middle vertex across a four-corner face and are closed under reflexivity, reversal, and composition. Edge rows certify the consecutive admissible edges of a list. A repeated initial vertex can be transported to the terminal end of any such edge row while preserving the number of vertex slots throughout.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/PauseSliding.lean, selected declaration lines 8-14, 16-22, 24-32, 34-38, 40-44, 46-58, 60-66, 68-74, 78-100; SHA-256 74a33f7e2c84a8197e653073232c964fe25ddec08be72e0eb9c5fdd1a9f59d86. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_RelativePathContraction
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
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! # Equal-slot pause transport through an entire edge row -/

namespace AbelianTargets

inductive FixedRowMoves {V : Type*} [DecidableEq V] (Face : Finset V → Prop) :
    List V → List V → Prop
  | refl (w) : FixedRowMoves Face w w
  | replace (a b b' c : V) (hf : Face {a,b,b',c}) (p s : List V) :
      FixedRowMoves Face (p++[a,b,c]++s) (p++[a,b',c]++s)
  | symm {w z} : FixedRowMoves Face w z → FixedRowMoves Face z w
  | trans {u v w} : FixedRowMoves Face u v → FixedRowMoves Face v w → FixedRowMoves Face u w

theorem FixedRowMoves.length_eq {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {w z : List V} (h : FixedRowMoves Face w z) : w.length = z.length := by
  induction h with
  | refl w => rfl
  | replace a b b' c hf p s => simp
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem FixedRowMoves.context {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {w z : List V} (h : FixedRowMoves Face w z) (p s : List V) :
    FixedRowMoves Face (p++w++s) (p++z++s) := by
  induction h with
  | refl w => exact .refl _
  | replace a b b' c hf p₀ s₀ =>
      simpa only [List.append_assoc] using FixedRowMoves.replace a b b' c hf (p++p₀) (s₀++s)
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem pause_slide_step {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {a b : V} (hface : Face {a,b}) : FixedRowMoves Face [a,a,b] [a,b,b] := by
  have heq : ({a,a,b,b} : Finset V) = {a,b} := by ext v; simp [or_assoc]
  have hf : Face {a,a,b,b} := heq ▸ hface
  simpa only [List.nil_append,List.append_nil] using FixedRowMoves.replace a a b b hf [] []

inductive EdgeRow {V : Type*} [DecidableEq V] (Face : Finset V → Prop) :
    V → List V → V → Prop
  | nil (a) : EdgeRow Face a [] a
  | cons {a b z tail} (hf : Face {a,b}) (h : EdgeRow Face b tail z) :
      EdgeRow Face a (b::tail) z

/-- A spare pause can be transported across every edge of the tail,
with exactly the same number of vertex slots throughout the sequence. -/
theorem EdgeRow.slide_pause_to_end {V : Type*} [DecidableEq V]
    {Face : Finset V → Prop} {a z : V} {tail : List V} (h : EdgeRow Face a tail z) :
    FixedRowMoves Face (a::a::tail) ((a::tail)++[z]) := by
  induction h with
  | nil a => exact .refl _
  | @cons a b z tail hf h ih =>
      have h₁ : FixedRowMoves Face (a::a::b::tail) (a::b::b::tail) := by
        simpa only [List.nil_append,List.cons_append,List.nil_append] using
          (pause_slide_step hf).context [] tail
      have h₂ := ih.context [a] []
      exact h₁.trans (by simpa only [List.cons_append,List.nil_append,List.append_nil] using h₂)

theorem FixedRowMoves.head_eq {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {w z : List V} (h : FixedRowMoves Face w z) : w.head? = z.head? := by
  induction h with
  | refl w => rfl
  | replace a b b' c hf p s => cases p <;> rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem FixedRowMoves.last_eq {V : Type*} [DecidableEq V] {Face : Finset V → Prop}
    {w z : List V} (h : FixedRowMoves Face w z) : w.getLast? = z.getLast? := by
  induction h with
  | refl w => rfl
  | replace a b b' c hf p s => cases s <;> simp
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

namespace IntervalCarriers

theorem WordPath.edgeRow {m K : ℕ} {A B : ℤ} {x z : Vertex} {w : List BSLetter}
    (hm : 1 ≤ m) (p : WordPath m x w z) :
    (∀ v ∈ p.vertices, v ∈ carrierVertices K A B) →
      EdgeRow (CarrierFace m K A B) x p.vertices.tail z := by
  induction p with
  | nil x => intro hp; exact .nil x
  | @cons s x y z w h p ih =>
      intro hp
      have hx : x ∈ carrierVertices K A B := hp x (by simp [WordPath.vertices])
      have hy : y ∈ carrierVertices K A B := hp y (by
        simp only [WordPath.vertices,List.mem_cons]
        exact Or.inr p.start_mem_vertices)
      have hf : CarrierFace m K A B {x,y} :=
        Or.inr (Or.inl ⟨x,hx,y,hy,h.adj hm,Finset.Subset.refl _⟩)
      have hp' : ∀ v ∈ p.vertices, v ∈ carrierVertices K A B := by
        intro v hv
        apply hp
        simp only [WordPath.vertices,List.mem_cons]
        exact Or.inr hv
      have hrow : p.vertices = y :: p.vertices.tail := by cases p <;> rfl
      change EdgeRow (CarrierFace m K A B) x p.vertices z
      rw [hrow]
      exact .cons hf (ih hp')

end IntervalCarriers

namespace FixedSlots

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]







end FixedSlots

end AbelianTargets


