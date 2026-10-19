-- Prove2me | Definitions.Def_AT260939824_AtlasControlledCellExtension
-- name    : AT260939824_AtlasControlledCellExtension
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:07:45.946435+00:00
-- url     : https://prove2.me/theorems/c8a714a2-e746-48d2-98ab-0cdff0b07a1f
-- title:
--   A controlled extension interface for one atlas cell
-- statement:
--   Let compatible lower-cell maps satisfy coordinate inequalities with constants $C_j$. Suppose the distinguished side of the parent cell has positive length and its carrier has a controlled contraction based at the left endpoint. The module assembles normalized prism boundary data and the actual endpoint-preserving cell extension.
--
--   The coordinate-bound predicate retains every physical-coordinate estimate explicitly, so it can be propagated in the quantitative rank construction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasControlledCellExtension.lean, selected declaration lines 13-18, 24-28, 32-36; SHA-256 3c3be16ae7aec5977cf5f387d43a3205e810755c37b2db7ed8c444f127d50f86. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryPathBounds
import Definitions.Def_AT260939824_AtlasBoundaryTransverseBounds
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
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

namespace LowerCellCarrierMaps

def CoordinateBounds (F : LowerCellCarrierMaps T m K i R) (C : Fin d→ℝ≥0) : Prop :=
  ∀ (k : Fin d) (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
    (z : RealCoordinates d) (x y : ℝ)
    (hx : Function.update z k x∈Q.closedBox) (hy : Function.update z k y∈Q.closedBox),
    dist (F.map Q hQ hrQ ⟨Function.update z k x,hx⟩)
      (F.map Q hQ hrQ ⟨Function.update z k y,hy⟩)≤C k*|x-y|

variable (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells) (hF : F.EndpointValues)
variable (C : Fin d→ℝ≥0) (hC : F.CoordinateBounds C)
variable (hi : R.lower i<R.upper i)

def controlledPrismData :
    PrismBoundaryData R i (cellLeftPoint m K i R) (cellRightPoint m K i R)
      (C i*(R.transverseWidth i).toNNReal) (prismTransverseBound R i C) :=
  F.prismBoundaryData hR hF _ _ (F.prism_path_lipschitz hR hi (C i) (hC i))
    (F.prism_transverse_lipschitz hR C hC)

variable {D J : ℝ≥0} (H : ControlledContraction (cellLeftPoint m K i R) D J)

/-- The local controlled extension uses the actual finite lower-cell
boundary and the actual carrier contraction. No extension existence is assumed. -/
def controlledCellExtension : EndpointCellCarrierExtension F hR :=
  F.relativeCellExtension hR hF hi H
    (F.prism_path_lipschitz hR hi (C i) (hC i)) (F.prism_transverse_lipschitz hR C hC)





end LowerCellCarrierMaps
end
end AbelianTargets


