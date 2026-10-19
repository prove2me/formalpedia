-- Prove2me | Definitions.Def_AT260939824_CarrierIntervalInclusion
-- name    : AT260939824_CarrierIntervalInclusion
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:49:53.420552+00:00
-- url     : https://prove2.me/theorems/077d6871-32a7-446f-b32b-3ea503c659a5
-- title:
--   Isometric inclusions of nested interval carriers
-- statement:
--   Let integer intervals satisfy $[C,D]\subseteq[A,B]$, and fix carrier base $m$ and height $K$. The vertex inclusion preserves each raw vertex, and pushforward of probability masses gives
--
--   $$ \mathcal C_m^K([C,D])\hookrightarrow\mathcal C_m^K([A,B]). $$
--
--   This map is an isometry, is the identity for equal intervals, and composes as expected along nested intervals. These are the inclusion maps used to compare values on nested atlas cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4–5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierIntervalInclusion.lean, selected declaration lines 9-13, 15-21, 23-25, 27-29, 31-47, 49-52, 54-60, 62-70, 72-76; SHA-256 1e17c0529715b66cedb67adeef5de994a0bc00c27109da5073d09d339ee70a14. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushGeometry
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
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

/-! Literal isometric inclusions of nested bounded interval carriers. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section
variable {m K : ℕ} {A B C D : ℤ}

theorem carrierTriangles_mono_interval (hAC : A ≤ C) (hDB : D ≤ B) :
    carrierTriangles m K C D ⊆ carrierTriangles m K A B := by
  intro t ht
  obtain ⟨c,hc,ht⟩ := Finset.mem_biUnion.mp ht
  exact Finset.mem_biUnion.mpr ⟨c,carrierCells_mono hAC hDB hc,ht⟩

theorem CarrierFace.mono_interval {s : Finset Vertex}
    (hs : CarrierFace m K C D s) (hAC : A ≤ C) (hDB : D ≤ B) : CarrierFace m K A B s := by
  rcases hs with ⟨v,hv,hsv⟩ | ⟨u,hu,v,hv,he,hsv⟩ | ⟨t,ht,hst⟩
  · exact Or.inl ⟨v,carrierVertices_mono hAC hDB hv,hsv⟩
  · exact Or.inr (Or.inl ⟨u,carrierVertices_mono hAC hDB hu,v,
      carrierVertices_mono hAC hDB hv,he,hsv⟩)
  · exact Or.inr (Or.inr ⟨t,carrierTriangles_mono_interval hAC hDB ht,hst⟩)

def intervalVertexInclusion (hAC : A ≤ C) (hDB : D ≤ B) :
    CarrierVertex K C D → CarrierVertex K A B :=
  fun v => ⟨v.val,carrierVertices_mono hAC hDB v.property⟩

theorem intervalVertexInclusion_injective (hAC : A ≤ C) (hDB : D ≤ B) :
    Function.Injective (intervalVertexInclusion (K := K) hAC hDB) :=
  fun v w he => Subtype.ext (congrArg (fun u : CarrierVertex K A B => u.val) he)

def intervalInclusion (hAC : A ≤ C) (hDB : D ≤ B) :
    Realization m K C D → Realization m K A B := by
  classical
  intro p
  let f := intervalVertexInclusion (K := K) hAC hDB
  refine ⟨Probability.push f p.val,?_⟩
  obtain ⟨s,hs,hp⟩ := p.property
  refine ⟨s.image f,?_,?_⟩
  · apply (mem_simplexFaces _).mpr
    have he : (s.image f).image Subtype.val=s.image Subtype.val := by
      simp only [Finset.image_image]
      rfl
    rw [he]
    exact ((mem_simplexFaces s).mp hs).mono_interval hAC hDB
  · intro w hw
    obtain ⟨v,hvw,hpv⟩ := (Probability.push_pos_iff f p.val w).mp hw
    exact Finset.mem_image.mpr ⟨v,hp v hpv,hvw⟩

@[simp] theorem intervalInclusion_val (hAC : A ≤ C) (hDB : D ≤ B)
    (p : Realization m K C D) :
    (intervalInclusion hAC hDB p).val=Probability.push (intervalVertexInclusion hAC hDB) p.val := by
  rfl

theorem intervalInclusion_isometry (hAC : A ≤ C) (hDB : D ≤ B) :
    Isometry (intervalInclusion (m := m) (K := K) hAC hDB) := by
  apply Isometry.of_dist_eq
  intro p q
  change dist (Probability.push (intervalVertexInclusion hAC hDB) p.val)
    (Probability.push (intervalVertexInclusion hAC hDB) q.val)=dist p.val q.val
  exact (Probability.isometry_push _ (intervalVertexInclusion_injective hAC hDB)).dist_eq p.val q.val

theorem intervalInclusion_comp {E F : ℤ}
    (hAC : A ≤ C) (hDB : D ≤ B) (hCE : C ≤ E) (hFD : F ≤ D)
    (p : Realization m K E F) :
    intervalInclusion hAC hDB (intervalInclusion hCE hFD p)=
      intervalInclusion (hAC.trans hCE) (hFD.trans hDB) p := by
  apply Subtype.ext
  rw [intervalInclusion_val]
  simp only [intervalInclusion_val,Probability.push_comp]
  rfl

theorem intervalInclusion_self (p : Realization m K A B) : intervalInclusion le_rfl le_rfl p=p := by
  apply Subtype.ext
  apply Probability.push_eq_self
  intro v hv
  exact Subtype.ext rfl

end
end AbelianTargets.IntervalCarriers


