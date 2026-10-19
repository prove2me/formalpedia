-- Prove2me | Definitions.Def_AT260939824_ParallelCollapse
-- name    : AT260939824_ParallelCollapse
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:07:20.214541+00:00
-- url     : https://prove2.me/theorems/06f6685a-8f04-4bf3-9bfd-77a932f81c7d
-- title:
--   Simultaneous free-edge triangle collapses
-- statement:
--   A collapse triangle consists of three pairwise distinct vertices. A free-collapse family inside a finite face complex certifies that every designated edge is free and that no other designated edge lies wholly in its triangle. Explicit finite compositions of the triangle homotopies define simultaneous maps on probability realizations, preserve the carrier, and keep each point in its original face or fixed.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/ParallelCollapse.lean, selected declaration lines 14-20, 24-26, 30-38, 41-46, 52-54, 56-62, 64-71, 73-88, 97-115, 117-120, 122-140, 142-146, 162-163, 165-192, 194-217; SHA-256 4f197d69b92ff3e09a39122e6b0cc892433b3f77d085ca31b22ee62f703c576b. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

/-! Simultaneous free-edge collapses, with track speed independent of the
number of triangles. These are actual finite compositions of PL maps. -/

namespace AbelianTargets
open scoped NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

structure CollapseTriangle (V : Type*) where
  a : V
  b : V
  c : V
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c

namespace CollapseTriangle
variable {V : Type*} [Fintype V]
def vertices (D : CollapseTriangle V) : Finset V := {D.a,D.b,D.c}
def homotopy (D : CollapseTriangle V) (p : Probability V) (t : unitInterval) :=
  Probability.triangleHomotopy D.a D.b D.c D.ab D.ac D.bc p t

theorem homotopy_supported (D : CollapseTriangle V) (p : Probability V)
    (hp : p.SupportedOn (D.vertices : Set V)) (t : unitInterval) :
    (D.homotopy p t).SupportedOn (D.vertices : Set V) := by
  have hp' : p.SupportedOn ({D.a,D.b,D.c} : Set V) := by simpa [vertices] using hp
  simpa [vertices,homotopy] using
    Probability.triangleHomotopy_supported D.a D.b D.c D.ab D.ac D.bc p hp' t
theorem homotopy_fixes (D : CollapseTriangle V) (p : Probability V)
    (hp : p.mass D.a = 0 ∨ p.mass D.b = 0) (t : unitInterval) : D.homotopy p t = p :=
  Probability.triangleHomotopy_fixes _ _ _ _ _ _ p hp t
end CollapseTriangle

structure FreeCollapseFamily {V : Type*} [Fintype V] (F : Finset (Finset V)) (I : Type*) where
  triangle : I → CollapseTriangle V
  mem_face : ∀ i, (triangle i).vertices ∈ F
  free_edge : ∀ i s, s ∈ F → (triangle i).a ∈ s → (triangle i).b ∈ s → s ⊆ (triangle i).vertices
  no_other_edge : ∀ i j, i ≠ j →
    (triangle j).a ∉ (triangle i).vertices ∨ (triangle j).b ∉ (triangle i).vertices

namespace FreeCollapseFamily
variable {V I : Type*} [Fintype V] {F : Finset (Finset V)}
variable (D : FreeCollapseFamily F I)

def mapList (D : FreeCollapseFamily F I) : List I → Probability V → unitInterval → Probability V
  | [],p,_ => p
  | i::l,p,t => (D.triangle i).homotopy (mapList D l p t) t

theorem fixes_other (i j : I) (hij : i ≠ j) (p : Probability V)
    (hp : p.SupportedOn ((D.triangle i).vertices : Set V)) (t : unitInterval) :
    (D.triangle j).homotopy p t = p := by
  apply CollapseTriangle.homotopy_fixes
  rcases D.no_other_edge i j hij with h | h
  · exact Or.inl (Probability.supportedOn_iff_zero.mp hp _ h)
  · exact Or.inr (Probability.supportedOn_iff_zero.mp hp _ h)

theorem mapList_fixes (l : List I) (p : Probability V)
    (hp : ∀ i ∈ l, p.mass (D.triangle i).a = 0 ∨ p.mass (D.triangle i).b = 0)
    (t : unitInterval) : D.mapList l p t = p := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [mapList,ih (fun j hj => hp j (List.mem_cons_of_mem i hj))]
    exact (D.triangle i).homotopy_fixes p (hp i (List.mem_cons_self)) t

theorem mapList_on_triangle (l : List I) (hl : l.Nodup) (i : I) (p : Probability V)
    (hp : p.SupportedOn ((D.triangle i).vertices : Set V)) (t : unitInterval) :
    D.mapList l p t = if i ∈ l then (D.triangle i).homotopy p t else p := by
  induction l with
  | nil => simp [mapList]
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    rw [mapList,ih hnodup.2]
    by_cases hij : i = j
    · subst j
      simp only [hnodup.1,if_false,List.mem_cons_self,if_true]
    · by_cases hi : i ∈ l
      · simp only [hi,if_true,List.mem_cons, hij, false_or]
        exact D.fixes_other i j hij _ ((D.triangle i).homotopy_supported p hp t) t
      · simp only [hi,if_false,List.mem_cons,hij,false_or]
        exact D.fixes_other i j hij p hp t



theorem mapList_joint (l : List I) :
    ∃ J : ℝ≥0, LipschitzWith J (fun z : Probability V × unitInterval => D.mapList l z.1 z.2) := by
  induction l with
  | nil =>
    refine ⟨1,LipschitzWith.of_dist_le_mul ?_⟩
    intro p q
    simpa only [mapList,Prod.dist_eq,NNReal.coe_one,one_mul] using
      le_max_left (dist p.1 q.1) (dist p.2 q.2)
  | cons i l ih =>
    obtain ⟨J,hJ⟩ := ih
    have hsnd : LipschitzWith 1 (Prod.snd : Probability V × unitInterval → unitInterval) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      simpa only [Prod.dist_eq,NNReal.coe_one,one_mul] using
        le_max_right (dist p.1 q.1) (dist p.2 q.2)
    refine ⟨4*max J 1,?_⟩
    simpa only [mapList] using
      (Probability.triangleHomotopy_joint (D.triangle i).a (D.triangle i).b (D.triangle i).c
        (D.triangle i).ab (D.triangle i).ac (D.triangle i).bc).comp (hJ.prodMk hsnd)

theorem mapList_zero (l : List I) (p : Probability V) : D.mapList l p 0 = p := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [mapList,ih,CollapseTriangle.homotopy,Probability.triangleHomotopy_zero]

theorem mapList_supported_or_eq (l : List I) (hl : l.Nodup) (p : SimplicialCarrier F)
    (t : unitInterval) :
    D.mapList l p.1 t = p.1 ∨
      ∃ i ∈ l, p.1.SupportedOn ((D.triangle i).vertices : Set V) ∧
        D.mapList l p.1 t = (D.triangle i).homotopy p.1 t := by
  by_cases h : ∃ i ∈ l, 0 < p.1.mass (D.triangle i).a ∧ 0 < p.1.mass (D.triangle i).b
  · obtain ⟨i,hi,ha,hb⟩ := h
    obtain ⟨s,hs,hp⟩ := p.2
    have hsub := D.free_edge i s hs (hp _ ha) (hp _ hb)
    have htri : p.1.SupportedOn ((D.triangle i).vertices : Set V) := fun v hv => hsub (hp v hv)
    exact Or.inr ⟨i,hi,htri,by rw [D.mapList_on_triangle l hl i p.1 htri t,if_pos hi]⟩
  · left
    apply D.mapList_fixes
    intro i hi
    have hn : ¬(0 < p.1.mass (D.triangle i).a ∧ 0 < p.1.mass (D.triangle i).b) :=
      fun hx => h ⟨i,hi,hx⟩
    rcases not_and_or.mp hn with ha | hb
    · exact Or.inl (le_antisymm (le_of_not_gt ha) (p.1.nonneg _))
    · exact Or.inr (le_antisymm (le_of_not_gt hb) (p.1.nonneg _))

def map (l : List I) (hl : l.Nodup) (p : SimplicialCarrier F) (t : unitInterval) : SimplicialCarrier F := by
  refine ⟨D.mapList l p.1 t,?_⟩
  rcases D.mapList_supported_or_eq l hl p t with h | ⟨i,hi,hp,h⟩
  · rw [h]; exact p.2
  · rw [h]; exact ⟨(D.triangle i).vertices,D.mem_face i,(D.triangle i).homotopy_supported p.1 hp t⟩





theorem map_zero (l : List I) (hl : l.Nodup) (p : SimplicialCarrier F) : D.map l hl p 0 = p :=
  Subtype.ext (D.mapList_zero l p.1)

theorem map_one_removes (l : List I) (hl : l.Nodup) (p : SimplicialCarrier F) (i : I) (hi : i ∈ l) :
    (D.map l hl p 1).1.mass (D.triangle i).a = 0 ∨
      (D.map l hl p 1).1.mass (D.triangle i).b = 0 := by
  by_cases h : ∃ j ∈ l, 0 < p.1.mass (D.triangle j).a ∧ 0 < p.1.mass (D.triangle j).b
  · obtain ⟨j,hj,ha,hb⟩ := h
    obtain ⟨s,hs,hp⟩ := p.2
    have hsub := D.free_edge j s hs (hp _ ha) (hp _ hb)
    have htri : p.1.SupportedOn ((D.triangle j).vertices : Set V) := fun v hv => hsub (hp v hv)
    change (D.mapList l p.1 1).mass _ = 0 ∨ (D.mapList l p.1 1).mass _ = 0
    rw [D.mapList_on_triangle l hl j p.1 htri 1,if_pos hj]
    by_cases hij : i = j
    · subst i
      simpa only [CollapseTriangle.homotopy,Probability.triangleHomotopy_one] using
        Probability.triangleCollapse_edge_removed (D.triangle j).a (D.triangle j).b (D.triangle j).c
          (D.triangle j).ab (D.triangle j).ac (D.triangle j).bc p.1
    · have hout := (D.triangle j).homotopy_supported p.1 htri 1
      rcases D.no_other_edge j i (Ne.symm hij) with ha | hb
      · exact Or.inl (Probability.supportedOn_iff_zero.mp hout _ ha)
      · exact Or.inr (Probability.supportedOn_iff_zero.mp hout _ hb)
  · have hfix : ∀ j ∈ l, p.1.mass (D.triangle j).a = 0 ∨ p.1.mass (D.triangle j).b = 0 := by
      intro j hj
      rcases not_and_or.mp (show ¬(0 < p.1.mass (D.triangle j).a ∧ 0 < p.1.mass (D.triangle j).b)
        from fun hx => h ⟨j,hj,hx⟩) with ha | hb
      · exact Or.inl (le_antisymm (le_of_not_gt ha) (p.1.nonneg _))
      · exact Or.inr (le_antisymm (le_of_not_gt hb) (p.1.nonneg _))
    change (D.mapList l p.1 1).mass _ = 0 ∨ (D.mapList l p.1 1).mass _ = 0
    rw [D.mapList_fixes l p.1 hfix 1]
    exact hfix i hi

theorem map_track (l : List I) (hl : l.Nodup) (p : SimplicialCarrier F) :
    LipschitzWith 1 (D.map l hl p) := by
  by_cases h : ∃ i ∈ l, 0 < p.1.mass (D.triangle i).a ∧ 0 < p.1.mass (D.triangle i).b
  · obtain ⟨i,hi,ha,hb⟩ := h
    obtain ⟨s,hs,hp⟩ := p.2
    have hsub := D.free_edge i s hs (hp _ ha) (hp _ hb)
    have htri : p.1.SupportedOn ((D.triangle i).vertices : Set V) := fun v hv => hsub (hp v hv)
    apply LipschitzWith.of_dist_le_mul
    intro r t
    change dist (D.mapList l p.1 r) (D.mapList l p.1 t) ≤ _
    rw [D.mapList_on_triangle l hl i p.1 htri r,D.mapList_on_triangle l hl i p.1 htri t,
      if_pos hi,if_pos hi]
    exact (Probability.triangleHomotopy_track _ _ _ _ _ _ p.1).dist_le_mul r t
  · apply LipschitzWith.of_dist_le_mul
    intro r t
    have hfix : ∀ i ∈ l, p.1.mass (D.triangle i).a = 0 ∨ p.1.mass (D.triangle i).b = 0 := by
      intro i hi
      rcases not_and_or.mp (show ¬(0 < p.1.mass (D.triangle i).a ∧ 0 < p.1.mass (D.triangle i).b)
        from fun hx => h ⟨i,hi,hx⟩) with ha | hb
      · exact Or.inl (le_antisymm (le_of_not_gt ha) (p.1.nonneg _))
      · exact Or.inr (le_antisymm (le_of_not_gt hb) (p.1.nonneg _))
    change dist (D.mapList l p.1 r) (D.mapList l p.1 t) ≤ _
    rw [D.mapList_fixes l p.1 hfix r,D.mapList_fixes l p.1 hfix t,dist_self]
    positivity

end FreeCollapseFamily
end
end AbelianTargets


