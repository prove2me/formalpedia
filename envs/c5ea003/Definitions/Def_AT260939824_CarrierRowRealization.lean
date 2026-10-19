-- Prove2me | Definitions.Def_AT260939824_CarrierRowRealization
-- name    : AT260939824_CarrierRowRealization
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:01:28.752547+00:00
-- url     : https://prove2.me/theorems/c887fbea-4bff-4ee5-9bc2-e03384535160
-- title:
--   Dirac charts for carrier vertex rows
-- statement:
--   Fix an interval carrier and a designated base vertex. Each raw carrier vertex is represented by its Dirac mass; the base gives a total fallback for raw vertices outside the carrier. Every permitted face then has a convex probability chart, with edge diameter at most one.
--
--   The module supplies the ambient face-chart interface needed to turn bounded triangle rows into continuous paths and homotopies in the literal carrier realization.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierRowRealization.lean, selected declaration lines 14-15, 17-19, 21-22, 24-44, 48-56; SHA-256 8902ce2950cbbe0bc05b40b8f01e1097bed06bcac588144c01661c26b641f580. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierCharts
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedRowRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleRowMoves
import Definitions.Def_AT260939824_WordPathHelpers
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
import Mathlib.Data.List.Chain
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

/-! Literal interval-carrier row moves, realized in barycentric coordinates. -/

namespace AbelianTargets

open scoped NNReal

noncomputable section

namespace IntervalCarriers

def liftVertex {K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) (v : Vertex) :
    CarrierVertex K A B := if h : v ∈ carrierVertices K A B then ⟨v,h⟩ else base

theorem liftVertex_val {K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) (v : Vertex)
    (hv : v ∈ carrierVertices K A B) : (liftVertex base v).1 = v := by
  simp only [liftVertex,dif_pos hv]

def vertexMass {K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) (v : Vertex) :
    CarrierVertex K A B → ℝ := (Probability.dirac (liftVertex base v)).mass

theorem carrierFace_charts {m K : ℕ} {A B : ℤ} (base : CarrierVertex K A B) :
    FaceCharts (CarrierFace m K A B) (vertexMass base) (ambientRealization m K A B) 1 := by
  refine ⟨?_,?_,?_⟩
  · intro s t h ht
    exact h.downward ht
  · intro s hs
    let t := s.image (liftVertex base)
    have ht : t.image Subtype.val = s := by
      ext v
      simp only [t,Finset.mem_image]
      constructor
      · rintro ⟨u,⟨w,hw,rfl⟩,rfl⟩
        simpa only [liftVertex_val base w (hs.vertices hw)] using hw
      · intro hv
        exact ⟨liftVertex base v,⟨v,hv,rfl⟩,liftVertex_val base v (hs.vertices hv)⟩
    refine ⟨Probability.faceChart t,Probability.faceChart_convex t,
      faceChart_subset_ambient t (ht ▸ hs),?_⟩
    intro v hv
    exact Probability.dirac_mem_faceChart t _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  · intro a b _
    exact Probability.dist_le_one _ _

end IntervalCarriers

theorem BoundedTriangleRows.length_bounds {V : Type*} [DecidableEq V]
    {Face : Finset V → Prop} {B : ℕ} {w u : List V} (h : BoundedTriangleRows Face B w u) :
    w.length ≤ B ∧ u.length ≤ B := by
  induction h with
  | refl w hw => exact ⟨hw,hw⟩
  | triangle a b c hf p s hw hu => exact ⟨hw,hu⟩
  | pause a p s hw hu => exact ⟨hw,hu⟩
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ⟨ih₁.1,ih₂.2⟩

namespace FixedSlots

variable {V E : Type*} [DecidableEq V] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Face : Finset V → Prop}



end FixedSlots

end

end AbelianTargets


