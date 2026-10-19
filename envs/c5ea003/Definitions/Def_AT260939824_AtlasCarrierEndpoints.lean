-- Prove2me | Definitions.Def_AT260939824_AtlasCarrierEndpoints
-- name    : AT260939824_AtlasCarrierEndpoints
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:03:16.74393+00:00
-- url     : https://prove2.me/theorems/b11737f9-25f7-4b8d-b6ad-f9164015e25e
-- title:
--   Distinguished bottom points of cell carriers
-- statement:
--   For a cell $R$, coordinate $i$, and integer $a\in[R_i^-,R_i^+]$, the bottom point is the Dirac mass at the carrier vertex $(a,0)$. Taking $a=R_i^-$ or $R_i^+$ gives the distinguished left and right endpoints. An endpoint-value predicate requires lower-cell maps to take these values on their corresponding end faces.
--
--   The boundary-value API preserves these endpoint conditions under carrier inclusions and boundary gluing.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4–5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasCarrierEndpoints.lean, selected declaration lines 8-10, 12-14, 16-25, 27-28, 30-31, 36-40, 42-58, 60-76; SHA-256 862e1bd6adf19185d62d14a8eec03e640b807c0b499231f760c61af46d0f0041. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FiniteRectangleIntersections
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.LocallyFinite
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

namespace AbelianTargets
noncomputable section
variable {d : ℕ} {m K : ℕ} {i : Fin d}

def cellBottomVertex (R : RectangularCell d) (i : Fin d) (a : ℤ)
    (ha : R.lower i≤a) (hb : a≤R.upper i) : IntervalCarriers.CarrierVertex K (R.lower i) (R.upper i) :=
  ⟨(a,0),IntervalCarriers.mem_carrierVertices.mpr ⟨ha,hb,Nat.zero_le K⟩⟩

def cellBottomPoint (R : RectangularCell d) (i : Fin d) (a : ℤ)
    (ha : R.lower i≤a) (hb : a≤R.upper i) : CellIntervalCarrier m K i R :=
  IntervalCarriers.point (cellBottomVertex R i a ha hb)

theorem cellIntervalInclude_bottomPoint {Q R : RectangularCell d}
    (hsub : Q.closedBox⊆R.closedBox) (a : ℤ) (ha : Q.lower i≤a) (hb : a≤Q.upper i) :
    cellIntervalInclude (m := m) (K := K) i hsub (cellBottomPoint Q i a ha hb)=
      cellBottomPoint R i a
        (((RectangularCell.closedBox_subset_iff Q R).mp hsub i).1.trans ha)
        (hb.trans ((RectangularCell.closedBox_subset_iff Q R).mp hsub i).2) := by
  apply Subtype.ext
  change Probability.push _ (Probability.dirac _)=Probability.dirac _
  rw [Probability.push_dirac]
  rfl

def cellLeftPoint (m K : ℕ) (i : Fin d) (R : RectangularCell d) : CellIntervalCarrier m K i R :=
  cellBottomPoint R i (R.lower i) le_rfl (R.ordered i)

def cellRightPoint (m K : ℕ) (i : Fin d) (R : RectangularCell d) : CellIntervalCarrier m K i R :=
  cellBottomPoint R i (R.upper i) (R.ordered i) le_rfl

namespace LowerCellCarrierMaps
variable {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀} {R : RectangularCell d}

def EndpointValues (F : LowerCellCarrierMaps T m K i R) : Prop :=
  ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hr : Q.rank<R.rank)
    (z : CellClosedDomain Q),
    (z.val i=(Q.lower i : ℝ) → F.map Q hQ hr z=cellLeftPoint m K i Q) ∧
    (z.val i=(Q.upper i : ℝ) → F.map Q hQ hr z=cellRightPoint m K i Q)

theorem boundaryValue_left (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (hF : F.EndpointValues) (z : CellBoundaryDomain R)
    (hz : z.val i=(R.lower i : ℝ)) : F.boundaryValue hR z=cellLeftPoint m K i R := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  have hlo : Q.lower i=R.lower i := by
    apply le_antisymm
    · exact_mod_cast (show (Q.lower i : ℝ)≤(R.lower i : ℝ) by rw [←hz]; exact (hzQ i).1)
    · exact ((RectangularCell.closedBox_subset_iff Q R).mp hQR i).1
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ]
  rw [(hF Q hQ hr ⟨z.val,hzQ⟩).1 (by simpa [hlo] using hz)]
  unfold cellLeftPoint
  rw [cellIntervalInclude_bottomPoint]
  simp only [hlo]

theorem boundaryValue_right (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (hF : F.EndpointValues) (z : CellBoundaryDomain R)
    (hz : z.val i=(R.upper i : ℝ)) : F.boundaryValue hR z=cellRightPoint m K i R := by
  let Q := T.pointCell z.val
  have hQ : Q∈T.cells := ⟨z.val,rfl⟩
  have hr : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR z.property
  have hQR := T.pointCell_subset_cell hR z.property.1
  have hzQ : z.val∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell z.val)
  have hhi : Q.upper i=R.upper i := by
    apply le_antisymm
    · exact ((RectangularCell.closedBox_subset_iff Q R).mp hQR i).2
    · exact_mod_cast (show (R.upper i : ℝ)≤(Q.upper i : ℝ) by rw [←hz]; exact (hzQ i).2)
  rw [F.boundaryValue_eq hR hQ hr hQR z hzQ]
  rw [(hF Q hQ hr ⟨z.val,hzQ⟩).2 (by simpa [hhi] using hz)]
  unfold cellRightPoint
  rw [cellIntervalInclude_bottomPoint]
  simp only [hhi]

end LowerCellCarrierMaps
end
end AbelianTargets


