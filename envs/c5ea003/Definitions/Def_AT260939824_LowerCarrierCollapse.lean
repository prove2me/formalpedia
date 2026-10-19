-- Prove2me | Definitions.Def_AT260939824_LowerCarrierCollapse
-- name    : AT260939824_LowerCarrierCollapse
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:10:37.504652+00:00
-- url     : https://prove2.me/theorems/6a1a0ac8-d961-4e25-9325-d96f176c6537
-- title:
--   Parallel collapse of presentation-polygon fans
-- statement:
--   At a fixed carrier height, polygon-fan stages are described by finite admissible faces. For base $m\ge1$ and each fan index below $m$, the relevant triangles form a certified family of free-edge collapses. Their actual simultaneous piecewise linear maps preserve the current simplicial carrier, track each point inside its original face, and remove the designated fan edges at the terminal parameter.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2-7; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure of Theorem 1.4 and Proposition 7.1; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/LowerCarrierCollapse.lean, selected declaration lines 13-17, 19-20, 22-25, 27-33, 35-50, 52-62, 64-68, 70-78, 80-115, 117-120, 125-127, 132-139; SHA-256 b9652023dbdc1ec97a204fd4574118f8e8a661bc401f05db69613a209fd90ff8. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierFaces
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplexMetricGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_UpperCarrierFaces
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

/-! Actual successive, simultaneous collapses of the lower polygon fans. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

def FanAdmissible (m K : ℕ) (A B : ℤ) (t : ℕ) (s : Finset Vertex) : Prop :=
  (∀ c : TopCell m K A B,
    ¬(upperLeft c.1.1 c.1.2 ∈ s ∧ upperRight m c.1.1 c.1.2 ∈ s)) ∧
  ∀ c : TopCell m K A B, ∀ k, t ≤ k → k < m →
    ¬(upperLeft c.1.1 c.1.2 ∈ s ∧ lowerVertex m c.1.1 c.1.2 (k+1) ∈ s)

def fanFaces (m K : ℕ) (A B : ℤ) (t : ℕ) : Finset (Finset (CarrierVertex (K+1) A B)) :=
  (simplexFaces m (K+1) A B).filter (fun s => FanAdmissible m K A B t (s.image Subtype.val))

@[simp] theorem mem_fanFaces {m K t : ℕ} {A B : ℤ} (s : Finset (CarrierVertex (K+1) A B)) :
    s ∈ fanFaces m K A B t ↔
      s ∈ simplexFaces m (K+1) A B ∧ FanAdmissible m K A B t (s.image Subtype.val) :=
  Finset.mem_filter

theorem lowerVertex_mem_lowerTriangle {m : ℕ} (hm : 1 ≤ m) (r : ℤ) (j n k : ℕ)
    (h : lowerVertex m r j k ∈ lowerTriangle m (r,j) n) : k = n ∨ k = n+1 := by
  simp only [lowerTriangle,Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with h | h | h
  · have hh := congrArg Prod.snd h; dsimp [lowerVertex,upperLeft] at hh; omega
  · exact Or.inl (lowerVertex_injective hm r j h)
  · exact Or.inr (lowerVertex_injective hm r j h)

theorem lowerTriangle_admissible {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (c : TopCell m K A B) : FanAdmissible m K A B (n+1) (lowerTriangle m c.1 n) := by
  constructor
  · intro d h
    have ha := top_mem_lowerTriangle (topCell_cell c) h.1 (by simp [upperLeft,topCell_height d])
    have hb := top_mem_lowerTriangle (topCell_cell c) h.2 (by simp [upperRight,topCell_height d])
    exact upperLeft_ne_upperRight hm d.1.1 d.1.2 (ha.trans hb.symm)
  · intro d k hk hkm h
    have ha := top_mem_lowerTriangle (topCell_cell c) h.1 (by simp [upperLeft,topCell_height d])
    have hr : d.1.1 = c.1.1 := by
      have hh := congrArg Prod.fst ha
      simpa only [upperLeft] using hh
    have hd : d = c := Subtype.ext (Prod.ext hr ((topCell_height d).trans (topCell_height c).symm))
    subst d
    have h' : lowerVertex m c.1.1 c.1.2 (k+1) ∈ lowerTriangle m (c.1.1,c.1.2) n := h.2
    rcases lowerVertex_mem_lowerTriangle hm _ _ _ _ h' with hkn | hkn <;> omega

def fanTriangle {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m) (c : TopCell m K A B) :
    CollapseTriangle (CarrierVertex (K+1) A B) where
  a := ⟨upperLeft c.1.1 c.1.2,upperLeft_mem_of_cell (topCell_cell c)⟩
  b := ⟨lowerVertex m c.1.1 c.1.2 (n+1),lowerVertex_mem_of_cell (topCell_cell c) (by omega)⟩
  c := ⟨lowerVertex m c.1.1 c.1.2 n,lowerVertex_mem_of_cell (topCell_cell c) (by omega)⟩
  ab := by intro h; have hh := congrArg (fun x => x.1.2) h; dsimp [upperLeft,lowerVertex] at hh; omega
  ac := by intro h; have hh := congrArg (fun x => x.1.2) h; dsimp [upperLeft,lowerVertex] at hh; omega
  bc := by
    intro h
    have hh := lowerVertex_injective hm c.1.1 c.1.2 (congrArg Subtype.val h)
    omega

theorem fanTriangle_image {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m) (c : TopCell m K A B) :
    (fanTriangle hm hn c).vertices.image Subtype.val = lowerTriangle m c.1 n := by
  ext v
  simp [CollapseTriangle.vertices,fanTriangle,lowerTriangle]
  tauto

theorem mem_fanTriangle_iff {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (c : TopCell m K A B) (v : CarrierVertex (K+1) A B) :
    v ∈ (fanTriangle hm hn c).vertices ↔ v.1 ∈ lowerTriangle m c.1 n := by
  rw [←fanTriangle_image hm hn c]
  constructor
  · intro h; exact Finset.mem_image.mpr ⟨v,h,rfl⟩
  · intro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    simpa only [(Subtype.ext he : w = v)] using hw

def fanCollapseFamily {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m) :
    FreeCollapseFamily (fanFaces m K A B (n+1)) (TopCell m K A B) where
  triangle := fanTriangle hm hn
  mem_face c := by
    apply (mem_fanFaces _).mpr
    constructor
    · apply (mem_simplexFaces _).mpr
      rw [fanTriangle_image]
      exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_lower (topCell_cell c) hn,Finset.Subset.refl _⟩)
    · rw [fanTriangle_image]
      exact lowerTriangle_admissible hm c
  free_edge c s hs ha hb := by
    obtain ⟨hs,hallowed⟩ := (mem_fanFaces s).mp hs
    have hs' := (mem_simplexFaces s).mp hs
    have ha' : upperLeft c.1.1 K ∈ s.image Subtype.val := by
      simpa only [fanTriangle,topCell_height c] using
        (Finset.mem_image.mpr ⟨(fanTriangle hm hn c).a,ha,rfl⟩ : (fanTriangle hm hn c).a.1 ∈ s.image Subtype.val)
    have hb' : lowerVertex m c.1.1 K (n+1) ∈ s.image Subtype.val := by
      simpa only [fanTriangle,topCell_height c] using
        (Finset.mem_image.mpr ⟨(fanTriangle hm hn c).b,hb,rfl⟩ : (fanTriangle hm hn c).b.1 ∈ s.image Subtype.val)
    have hsub := lower_edge_free hm hn hs' ha' hb' hallowed.1
      (fun hnm d => hallowed.2 d (n+1) le_rfl hnm)
    intro v hv
    apply (mem_fanTriangle_iff hm hn c v).mpr
    have hc : c.1 = (c.1.1,K) := Prod.ext rfl (topCell_height c)
    rw [hc]
    exact hsub (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  no_other_edge c d hcd := by
    left
    intro h
    have hmem := (mem_fanTriangle_iff hm hn c (fanTriangle hm hn d).a).mp h
    have he := top_mem_lowerTriangle (topCell_cell c) hmem (by simp [fanTriangle,upperLeft,topCell_height d])
    have hr : d.1.1 = c.1.1 := by
      have hh := congrArg Prod.fst he
      simpa only [fanTriangle,upperLeft] using hh
    exact hcd (Subtype.ext (Prod.ext hr.symm ((topCell_height c).trans (topCell_height d).symm)))

def collapseFan {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) (t : unitInterval) :
    SimplicialCarrier (fanFaces m K A B (n+1)) :=
  (fanCollapseFamily hm hn).map (Finset.univ.toList) (Finset.nodup_toList _) p t


theorem collapseFan_track {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) : LipschitzWith 1 (collapseFan hm hn p) :=
  (fanCollapseFamily hm hn).map_track _ (Finset.nodup_toList _) p

@[simp] theorem collapseFan_zero {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) : collapseFan hm hn p 0 = p :=
  (fanCollapseFamily hm hn).map_zero _ (Finset.nodup_toList _) p
theorem collapseFan_removes {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : SimplicialCarrier (fanFaces m K A B (n+1))) (c : TopCell m K A B) :
    (collapseFan hm hn p 1).1.mass (fanTriangle hm hn c).a = 0 ∨
      (collapseFan hm hn p 1).1.mass (fanTriangle hm hn c).b = 0 :=
  (fanCollapseFamily hm hn).map_one_removes _ (Finset.nodup_toList _) p c (by simp)

end
end AbelianTargets.IntervalCarriers


