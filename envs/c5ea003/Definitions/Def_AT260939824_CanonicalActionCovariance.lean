-- Prove2me | Definitions.Def_AT260939824_CanonicalActionCovariance
-- name    : AT260939824_CanonicalActionCovariance
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:34:08.319213+00:00
-- url     : https://prove2.me/theorems/1103871f-840f-4392-9df4-794519fd6a2f
-- title:
--   Pullback of a lattice action by the parity shear
-- statement:
--   For $d\ge1$, let $\sigma:\mathbb Z^d\to\mathbb Z^d$ be the parity-coordinate automorphism. Given a lattice action on $X$, its sheared version has the same underlying points and topology, and the action
--
--   $$g\mathbin{\odot}x=\sigma^{-1}(g)\cdot x.$$
--
--   The identity maps between the original and sheared spaces are inverse continuous maps. They identify original translation by $g$ with sheared translation by $\sigma(g)$. Polishness is inherited, and a continuous original action gives a continuous sheared action. These definitions let a construction expressed through parity in one distinguished coordinate be applied after a change of lattice coordinates.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 2.1, 6–7; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/CanonicalActionCovariance.lean, selected declaration lines 198-200, 206, 208, 210-211, 213-214, 216-217, 219-220, 222-223, 225-226, 231-240, 242-244, 246-251, 253-262; SHA-256 c8c0edd329c88d0a8523c9d49eecf1bb9a5a1c833f20443f8c80b33ad3a67d7b. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
import Definitions.Def_AT260939824_AtlasRankRecursion
import Definitions.Def_AT260939824_AtlasRelativeCellExtension
import Definitions.Def_AT260939824_BottomEdgeSplice
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

set_option autoImplicit false

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

/-- The original space equipped with the lattice action pulled back along
the inverse parity shear. The underlying points and topology are unchanged. -/
def ParitySheared {d : ℕ} (_hd : 1 ≤ d) (X : Type*) := X

namespace ParitySheared

variable {d : ℕ} (hd : 1 ≤ d) {X : Type*}

def ofOriginal (x : X) : ParitySheared hd X := x

def toOriginal (x : ParitySheared hd X) : X := x

@[simp] theorem toOriginal_ofOriginal (x : X) :
    toOriginal hd (ofOriginal hd x) = x := rfl

@[simp] theorem ofOriginal_toOriginal (x : ParitySheared hd X) :
    ofOriginal hd (toOriginal hd x) = x := rfl

instance [TopologicalSpace X] : TopologicalSpace (ParitySheared hd X) :=
  inferInstanceAs (TopologicalSpace X)

instance [TopologicalSpace X] [PolishSpace X] : PolishSpace (ParitySheared hd X) :=
  inferInstanceAs (PolishSpace X)

theorem continuous_ofOriginal [TopologicalSpace X] :
    Continuous (ofOriginal hd : X → ParitySheared hd X) := continuous_id

theorem continuous_toOriginal [TopologicalSpace X] :
    Continuous (toOriginal hd : ParitySheared hd X → X) := continuous_id



instance [AddAction (Lattice d) X] : AddAction (Lattice d) (ParitySheared hd X) where
  vadd g x := ofOriginal hd ((parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x)
  zero_vadd x := by
    change ofOriginal hd ((parityCoordinateEquiv hd).symm 0 +ᵥ toOriginal hd x) = x
    simp
  add_vadd g h x := by
    change ofOriginal hd ((parityCoordinateEquiv hd).symm (g+h) +ᵥ toOriginal hd x) =
      ofOriginal hd ((parityCoordinateEquiv hd).symm g +ᵥ
        ((parityCoordinateEquiv hd).symm h +ᵥ toOriginal hd x))
    rw [map_add, add_vadd]

@[simp] theorem toOriginal_vadd [AddAction (Lattice d) X]
    (g : Lattice d) (x : ParitySheared hd X) :
    toOriginal hd (g +ᵥ x) = (parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x := rfl

@[simp] theorem ofOriginal_vadd [AddAction (Lattice d) X]
    (g : Lattice d) (x : X) :
    ofOriginal hd (g +ᵥ x) = shearCoordinates hd g +ᵥ ofOriginal hd x := by
  change ofOriginal hd (g +ᵥ x) =
    ofOriginal hd ((parityCoordinateEquiv hd).symm (parityCoordinateEquiv hd g) +ᵥ x)
  rw [AddEquiv.symm_apply_apply]

instance [TopologicalSpace X] [AddAction (Lattice d) X]
    [ContinuousVAdd (Lattice d) X] : ContinuousVAdd (Lattice d) (ParitySheared hd X) where
  continuous_vadd := by
    apply continuous_prod_of_discrete_left.mpr
    intro g
    change Continuous (fun x : ParitySheared hd X =>
      ofOriginal hd ((parityCoordinateEquiv hd).symm g +ᵥ toOriginal hd x))
    exact (continuous_ofOriginal hd).comp
      ((continuous_const_vadd ((parityCoordinateEquiv hd).symm g)).comp
        (continuous_toOriginal hd))



end ParitySheared
end AbelianTargets


