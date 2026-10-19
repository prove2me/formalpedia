-- Prove2me | solution 1 for AbelianTargets.proposition7_1
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:20:24.805484+00:00
-- url     : https://prove2.me/submissions/d9098157-934c-446a-aba8-004993d6cede

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_AtlasScaleParameters
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalActionCovariance
import Definitions.Def_AT260939824_CanonicalIntervalContractions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_CarrierProjectionGluing
import Definitions.Def_AT260939824_CarrierProjectionNaturality
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ConeDomainNaturality
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntegerPrismTranslation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativeContractionNaturality
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SmallStepProjectedOrbitMaps
import Definitions.Def_AT260939824_Statements
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_VerticalCarrierCollapse
import Definitions.Def_AT260939824_WordPathHelpers
import Definitions.Def_AbelianTargets260939824Actions
import Definitions.Def_AbelianTargets260939824ReducedWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
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
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
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
import Theorems.Thm_AbelianTargets_approximateParityMaps_supportPair
import Theorems.Thm_AbelianTargets_hasContinuousHom_of_probabilityField
import Theorems.Thm_AbelianTargets_probabilityField_of_approximateParityMaps
import Theorems.Thm_AbelianTargets_supportTorsionData_of_oddTorsion

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.SupportModel
section
/-!
# The analytic implication in Section 6

This file checks composition with an equivariant support model, choice of
a uniform error on a compact source, and exact graph rounding.
The actual presentation complex is constructed in separate modules;
existence of its approximate parity maps remains an explicit geometric input.
-/

namespace AbelianTargets







/-- Complete formalization of the closing argument in Section 6, conditional
on the two independent geometric inputs. -/
theorem hasContinuousHom_of_supportModel
    {d : ℕ} {X Y V : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [MetricSpace Y] [CompactSpace Y]
    [Fintype V] [Nonempty V] [TopologicalSpace V]
    {H : SimpleGraph V} {τ : Y → Y}
    (model : SupportModel H τ)
    (approx : ApproximateParityMaps (d := d) X Y τ) :
    HasContinuousHom (d := d) (X := X) H := by
  obtain ⟨field⟩ := probabilityField_of_approximateParityMaps model approx
  exact hasContinuousHom_of_probabilityField field

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.SupportGeometry
section
/-!
# Concrete probability support geometry

The space `SupportPair H` is the support space `𝒟(H)` in Lemma 6.2 of
arXiv:2609.39824.  Its shore swap is a free involution.  Convex interpolation
inside a fixed shore gives the graph-edge paths, and interpolation of both
shores gives the square filling for a four-walk.  These are actual continuous
maps, not assumptions about an auxiliary presentation complex.
-/

open scoped BigOperators unitInterval

namespace AbelianTargets

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

attribute [local instance] Classical.propDecidable











































end Probability

variable {V : Type*} [Fintype V] (H : SimpleGraph V)















namespace SupportPair
































/-- Approximate swap maps into the concrete compact support complex already
suffice for exact continuous graph coloring. -/
theorem hasContinuousHom_of_approximateSwap
    {d : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
    [Nonempty V] [TopologicalSpace V]
    (approx : ApproximateParityMaps (d := d) X (SupportPair H) (swap H)) :
    HasContinuousHom (d := d) (X := X) H :=
  hasContinuousHom_of_supportModel (model H) approx





































































end SupportPair

end

end AbelianTargets

end

/-!
# Theorem 1.4 and Proposition 7.1 in every positive dimension

The actual canonical atlas maps on the inverse-sheared action provide
finite-range approximate shore-swap maps. Each original generator becomes
one or two coordinate steps. The constructed torsion support data and the
checked probability rounding then give the requested graph homomorphism.
There is no additional geometric-construction hypothesis.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
universe u v

theorem solution {V : Type v} [TopologicalSpace V] [Fintype V]
    [DiscreteTopology V] (H : SimpleGraph V) :
    Proposition71Statement.{u} H := by
  intro ht d hd X _ _ _ _ zeroDim free
  obtain ⟨D⟩ := supportTorsionData_of_oddTorsion H ht
  letI : Nonempty V := D.base.left.nonempty
  exact SupportPair.hasContinuousHom_of_approximateSwap H
    (approximateParityMaps_supportPair D hd zeroDim free)
