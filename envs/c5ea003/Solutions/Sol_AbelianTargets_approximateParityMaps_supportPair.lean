-- Prove2me | solution 1 for AbelianTargets.approximateParityMaps_supportPair
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:18:50.201249+00:00
-- url     : https://prove2.me/submissions/f987ff08-369d-4fa7-a5a6-eea8c99d2448

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
import Definitions.Def_AT260939824_ParitySwapGeometry
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
import Theorems.Thm_AbelianTargets_approximateParityMaps_of_latticeOrbitConstruction
import Theorems.Thm_AbelianTargets_exists_smallStepLatticeOrbitMap

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.ParityCoordinates
section
/-!
# The unimodular parity coordinate change in Proposition 6.1

The new first coordinate is the sum of the original coordinates. Hence
every original generator has first coordinate one, and each of the
remaining generators changes only one transverse coordinate as well.
-/

namespace AbelianTargets

open scoped BigOperators

















theorem shearCoordinates_generator_first {d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    shearCoordinates hd (unitVector i) (firstAxis hd) = 1 := by
  simp [shearCoordinates, unitVector]





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




























theorem isometry_swap : Isometry (swap H) := by
  apply Isometry.of_dist_eq
  intro z w
  change max (dist z.right w.right) (dist z.left w.left) =
    max (dist z.left w.left) (dist z.right w.right)
  exact max_comm _ _









































































end SupportPair

end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.CanonicalActionCovariance
section
/-!
# Action covariance and integer-lattice parity closing

The actual canonical atlas projection commutes with repointing by the lattice
shift and the corresponding support-shore parity. Integer-lattice unit edges
suffice for the final generator comparison after the parity shear.
-/

namespace AbelianTargets
noncomputable section
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000





section Action
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable {M₀ : AnisotropicClopenMarkers d L X} {S : ℕ}
variable {W : Type*} [Fintype W] {G : SimpleGraph W}







end Action






end
end AbelianTargets

namespace AbelianTargets



namespace ParitySheared

variable {d : ℕ} (hd : 1 ≤ d) {X : Type*}

















theorem zeroDimensional [TopologicalSpace X] (hX : ZeroDimensional X) :
    ZeroDimensional (ParitySheared hd X) := hX









theorem isFree [AddAction (Lattice d) X]
    (hX : IsFree (G := Lattice d) (X := X)) :
    IsFree (G := Lattice d) (X := ParitySheared hd X) := by
  intro g x hx
  have hfix : (parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x = toOriginal hd x :=
    congrArg (toOriginal hd) hx
  have hg := hX ((parityCoordinateEquiv hd).symm g) (toOriginal hd x) hfix
  apply (parityCoordinateEquiv hd).symm.injective
  simpa using hg

end ParitySheared
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

theorem solution
    {d : ℕ} {X : Type u} {V : Type v}
    [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X]
    [Fintype V] {H : SimpleGraph V} (D : SupportTorsionData H)
    (hd : 1 ≤ d) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X)) :
    ApproximateParityMaps (d := d) X (SupportPair H) (SupportPair.swap H) := by
  classical
  apply approximateParityMaps_of_latticeOrbitConstruction hd (SupportPair.isometry_swap H)
  intro ε hε
  obtain ⟨F⟩ := exists_smallStepLatticeOrbitMap (X := ParitySheared hd X)
    D (firstAxis hd) (ParitySheared.zeroDimensional hd zeroDim)
      (ParitySheared.isFree hd free) hε
  refine ⟨fun x g => F.orbitMap (ParitySheared.ofOriginal hd x) g,
    F.continuous_origin.comp (ParitySheared.continuous_ofOriginal hd), ?_, ?_, ?_⟩
  · apply F.finite_range_origin.subset
    rintro y ⟨x, rfl⟩
    exact ⟨ParitySheared.ofOriginal hd x, rfl⟩
  · intro x i
    change F.orbitMap (ParitySheared.ofOriginal hd (unitVector i +ᵥ x)) 0 =
      SupportPair.swap H
        (F.orbitMap (ParitySheared.ofOriginal hd x) (shearCoordinates hd (unitVector i)))
    rw [ParitySheared.ofOriginal_vadd]
    have hc := F.covariance (ParitySheared.ofOriginal hd x)
      (shearCoordinates hd (unitVector i))
    rw [shearCoordinates_generator_first] at hc
    simpa [SupportPair.paritySwap] using hc
  · intro x i g
    exact F.unit_step (ParitySheared.ofOriginal hd x) i g
