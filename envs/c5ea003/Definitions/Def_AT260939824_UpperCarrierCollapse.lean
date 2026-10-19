-- Prove2me | Definitions.Def_AT260939824_UpperCarrierCollapse
-- name    : AT260939824_UpperCarrierCollapse
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:08:29.297118+00:00
-- url     : https://prove2.me/theorems/58bd3671-52ae-4898-8c20-f2125a0d27ba
-- title:
--   Simultaneous collapse of upper carrier triangles
-- statement:
--   Let $m\ge1$, $K\in\mathbb N$, and $A,B\in\mathbb Z$. In the height-$(K+1)$ carrier over $[A,B]$, let top cells be presentation cells based at height $K$. For each such cell, form the triangle with the two upper vertices and the lower right vertex. Its upper edge is free in the carrier face system, and no other selected triangle contains that free edge. The finite family therefore defines a simultaneous collapse
--   $$H_{\mathrm{top}}:|C_{m,K+1}[A,B]|\times I\to|C_{m,K+1}[A,B]|.$$
--   Each time track is $1$-Lipschitz. At time one, in every top triangle at least one upper-edge endpoint has zero mass. This removes all top horizontal edges before the remaining fan collapses. At time zero the collapse is the identity on every carrier point.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/UpperCarrierCollapse.lean, selected declaration lines 14-18, 20-23, 25-32, 34-38, 40-49, 51-85, 87-89, 95-96, 103-104, 106-110; SHA-256 b8a1505279f0ff97d45e2c463711dc568a01055fdb1d32b864660cb006599b91. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
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

/-! A simultaneous, continuous, speed-one collapse of all top horizontal
edges in the literal finite interval carrier. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

def topCells (m K : ℕ) (A B : ℤ) : Finset Vertex :=
  (carrierCells m (K+1) A B).filter (fun c => c.2 = K)
abbrev TopCell (m K : ℕ) (A B : ℤ) := {c : Vertex // c ∈ topCells m K A B}
instance (m K : ℕ) (A B : ℤ) : Fintype (TopCell m K A B) :=
  Fintype.ofFinset (topCells m K A B) (by simp)

theorem topCell_cell {m K : ℕ} {A B : ℤ} (c : TopCell m K A B) :
    c.1 ∈ carrierCells m (K+1) A B := (Finset.mem_filter.mp c.2).1
theorem topCell_height {m K : ℕ} {A B : ℤ} (c : TopCell m K A B) : c.1.2 = K :=
  (Finset.mem_filter.mp c.2).2

def topTriangle {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (c : TopCell m K A B) :
    CollapseTriangle (CarrierVertex (K+1) A B) where
  a := ⟨upperLeft c.1.1 c.1.2,upperLeft_mem_of_cell (topCell_cell c)⟩
  b := ⟨upperRight m c.1.1 c.1.2,upperRight_mem_of_cell (topCell_cell c)⟩
  c := ⟨lowerVertex m c.1.1 c.1.2 m,lowerVertex_mem_of_cell (topCell_cell c) le_rfl⟩
  ab := fun h => upperLeft_ne_upperRight hm c.1.1 c.1.2 (congrArg Subtype.val h)
  ac := by intro h; have hh := congrArg (fun x => x.1.2) h; dsimp [upperLeft,lowerVertex] at hh; omega
  bc := by intro h; have hh := congrArg (fun x => x.1.2) h; dsimp [upperRight,lowerVertex] at hh; omega

theorem topTriangle_image {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (c : TopCell m K A B) :
    (topTriangle hm c).vertices.image Subtype.val = upperTriangle m c.1 := by
  ext v
  simp [CollapseTriangle.vertices,topTriangle,upperTriangle]
  tauto

theorem mem_topTriangle_iff {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (c : TopCell m K A B)
    (v : CarrierVertex (K+1) A B) :
    v ∈ (topTriangle hm c).vertices ↔ v.1 ∈ upperTriangle m c.1 := by
  rw [←topTriangle_image hm c]
  constructor
  · intro h; exact Finset.mem_image.mpr ⟨v,h,rfl⟩
  · rintro h
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp h
    have hwv : w = v := Subtype.ext he
    simpa only [hwv] using hw

def topCollapseFamily {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) :
    FreeCollapseFamily (simplexFaces m (K+1) A B) (TopCell m K A B) where
  triangle := topTriangle hm
  mem_face c := by
    apply (mem_simplexFaces _).mpr
    rw [topTriangle_image]
    exact Or.inr (Or.inr ⟨_,mem_carrierTriangles_upper (topCell_cell c),Finset.Subset.refl _⟩)
  free_edge c s hs ha hb := by
    have hs' := (mem_simplexFaces s).mp hs
    have ha' : upperLeft c.1.1 K ∈ s.image Subtype.val := by
      simpa only [topTriangle,topCell_height c] using
        (Finset.mem_image.mpr ⟨(topTriangle hm c).a,ha,rfl⟩ : (topTriangle hm c).a.1 ∈ s.image Subtype.val)
    have hb' : upperRight m c.1.1 K ∈ s.image Subtype.val := by
      simpa only [topTriangle,topCell_height c] using
        (Finset.mem_image.mpr ⟨(topTriangle hm c).b,hb,rfl⟩ : (topTriangle hm c).b.1 ∈ s.image Subtype.val)
    have hsub := upper_edge_free hm hs' ha' hb'
    intro v hv
    apply (mem_topTriangle_iff hm c v).mpr
    have hc : c.1 = (c.1.1,K) := Prod.ext rfl (topCell_height c)
    rw [hc]
    exact hsub (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  no_other_edge c d hcd := by
    by_contra h
    push Not at h
    have ha := (mem_topTriangle_iff hm c (topTriangle hm d).a).mp h.1
    have hb := (mem_topTriangle_iff hm c (topTriangle hm d).b).mp h.2
    have hc : c.1 = (c.1.1,K) := Prod.ext rfl (topCell_height c)
    have hd : d.1 = (d.1.1,K) := Prod.ext rfl (topCell_height d)
    change upperLeft d.1.1 d.1.2 ∈ upperTriangle m c.1 at ha
    change upperRight m d.1.1 d.1.2 ∈ upperTriangle m c.1 at hb
    rw [hc,topCell_height d] at ha hb
    have hr := upper_edge_origin_eq hm ha hb
    apply hcd
    apply Subtype.ext
    exact Prod.ext hr.symm ((topCell_height c).trans (topCell_height d).symm)

def collapseTop {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m (K+1) A B) (t : unitInterval) : Realization m (K+1) A B :=
  (topCollapseFamily hm).map (Finset.univ.toList) (Finset.nodup_toList _) p t



theorem collapseTop_track {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    LipschitzWith 1 (collapseTop hm p) := (topCollapseFamily hm).map_track _ (Finset.nodup_toList _) p



@[simp] theorem collapseTop_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B) :
    collapseTop hm p 0 = p := (topCollapseFamily hm).map_zero _ (Finset.nodup_toList _) p

theorem collapseTop_removes {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m) (p : Realization m (K+1) A B)
    (c : TopCell m K A B) :
    (collapseTop hm p 1).1.mass (topTriangle hm c).a = 0 ∨
      (collapseTop hm p 1).1.mass (topTriangle hm c).b = 0 :=
  (topCollapseFamily hm).map_one_removes _ (Finset.nodup_toList _) p c (by simp)

end
end AbelianTargets.IntervalCarriers


