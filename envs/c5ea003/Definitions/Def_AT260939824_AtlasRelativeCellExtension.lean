-- Prove2me | Definitions.Def_AT260939824_AtlasRelativeCellExtension
-- name    : AT260939824_AtlasRelativeCellExtension
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:05:24.359711+00:00
-- url     : https://prove2.me/theorems/b1298b09-8f7b-47f8-9b48-4890f59d7a41
-- title:
--   Relative cell extensions with prescribed endpoints
-- statement:
--   For a cell $R$, compatible lower-cell maps define its boundary values. An endpoint extension is a continuous carrier map on the closed cell that agrees with those values and sends the two distinguished end faces to the left and right bottom points. With positive longitudinal width, controlled boundary data and a based contraction provide the extension; a collapsed longitudinal side has a constant extension.
--
--   The interface handles both geometric cases within the same rank construction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasRelativeCellExtension.lean, selected declaration lines 9-12, 17-28, 30-43, 45-55; SHA-256 bf985c39d1a6d0e83972ee62f39a5f5763d62f1e225a66b22882e777a850e239. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
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
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

structure EndpointCellCarrierExtension (F : LowerCellCarrierMaps T m K i R)
    (hR : R∈T.cells) extends CellCarrierExtension F hR where
  source : ∀ z : CellClosedDomain R,z.val i=(R.lower i : ℝ) → map z=cellLeftPoint m K i R
  target : ∀ z : CellClosedDomain R,z.val i=(R.upper i : ℝ) → map z=cellRightPoint m K i R

namespace LowerCellCarrierMaps
variable (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells) (hF : F.EndpointValues)

def prismBoundaryData (S B : ℝ≥0)
    (hpath : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),LipschitzWith S
      (fun r => F.boundaryValue hR (prismBoundaryPoint R i v r)))
    (htrans : ∀ r : unitInterval,LipschitzWith B
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) =>
        F.boundaryValue hR (prismBoundaryPoint R i v r))) :
    PrismBoundaryData R i (cellLeftPoint m K i R) (cellRightPoint m K i R) S B where
  map := F.boundaryMap hR
  source := F.boundaryValue_left hR hF
  target := F.boundaryValue_right hR hF
  path_lipschitz := hpath
  transverse := htrans

/-- Actual relative extension when the distinguished side has positive
length. Its only analytic input is the stated quantitative boundary data. -/
def relativeCellExtension {S B D J : ℝ≥0} (hi : R.lower i<R.upper i)
    (H : ControlledContraction (cellLeftPoint m K i R) D J)
    (hpath : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),LipschitzWith S
      (fun r => F.boundaryValue hR (prismBoundaryPoint R i v r)))
    (htrans : ∀ r : unitInterval,LipschitzWith B
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) =>
        F.boundaryValue hR (prismBoundaryPoint R i v r))) :
    EndpointCellCarrierExtension F hR where
  map := (F.prismBoundaryData hR hF S B hpath htrans).continuousMap H hi
  boundary := (F.prismBoundaryData hR hF S B hpath htrans).fill_boundary H hi
  source := (F.prismBoundaryData hR hF S B hpath htrans).fill_source H hi
  target := (F.prismBoundaryData hR hF S B hpath htrans).fill_target H hi

/-- A stratum with collapsed distinguished coordinate is assigned its
literal height-zero vertex; the already-built boundary has the same value. -/
def collapsedCellExtension (hi : R.lower i=R.upper i) : EndpointCellCarrierExtension F hR where
  map := ContinuousMap.const _ (cellLeftPoint m K i R)
  boundary z := by
    apply (F.boundaryValue_left hR hF z ?_).symm
    exact le_antisymm (by simpa [hi] using (z.property.1 i).2) (z.property.1 i).1
  source z hz := rfl
  target z hz := by
    change cellLeftPoint m K i R=cellRightPoint m K i R
    simp only [cellLeftPoint,cellRightPoint,cellBottomPoint,cellBottomVertex,hi]

end LowerCellCarrierMaps
end
end AbelianTargets


