-- Prove2me | Definitions.Def_AT260939824_AtlasQuantitativeRecursion
-- name    : AT260939824_AtlasQuantitativeRecursion
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:10:28.709435+00:00
-- url     : https://prove2.me/theorems/1102f89b-a9f6-40e7-b18a-974b01f0d571
-- title:
--   Coordinate-controlled endpoint skeleton families
-- statement:
--   Let $R$ be an atlas cell and let $f$ map its closed box into its interval carrier. A coordinate-bound vector $C$ requires
--
--   $$ d(f(z),f(z'))\le C_j|z_j-z'_j| $$
--
--   whenever $z$ and $z'$ differ only in coordinate $j$. A quantitative endpoint skeleton family combines these bounds with continuous maps, inclusion compatibility, and end-face values on all cells below a rank threshold. Its next-stage constructor accepts the precise bounds for the new cells.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasQuantitativeRecursion.lean, selected declaration lines 13-16, 18-21, 26-28, 30-46, 48-58, 65-68, 70-94, 96-102; SHA-256 21ebf1e95040878b860bef3fe0780b6112903244abf1a071909d7a6202751102. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasCarrierEndpoints
import Definitions.Def_AT260939824_AtlasEndpointRecursion
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
import Definitions.Def_AT260939824_IntegerPrismEstimates
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace AbelianTargets
noncomputable section
open scoped NNReal unitInterval
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

def CellCoordinateBounds (R : RectangularCell d)
    (f : CellClosedDomain R → CellIntervalCarrier m K i R) (C : Fin d→ℝ≥0) : Prop :=
  ∀ j (z z' : CellClosedDomain R),(∀ k,k≠j → z.val k=z'.val k) →
    dist (f z) (f z')≤C j*|z.val j-z'.val j|

structure QuantitativeEndpointSkeletonCarrierMaps (T : IntegerRectangularTiling d K₀)
    (m K : ℕ) (i : Fin d) (n : ℕ) (C : Fin d→ℝ≥0)
    extends EndpointSkeletonCarrierMaps T m K i n where
  coordinate_bounds : ∀ R hR hr,CellCoordinateBounds R (map R hR hr) C

namespace QuantitativeEndpointSkeletonCarrierMaps
variable {n : ℕ} {C C' : Fin d→ℝ≥0}

def empty : QuantitativeEndpointSkeletonCarrierMaps T m K i 0 C where
  toEndpointSkeletonCarrierMaps := EndpointSkeletonCarrierMaps.empty
  coordinate_bounds R hR hr := (Nat.not_lt_zero _ hr).elim

def next (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C)
    (extend : ∀ (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n),
      EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR)
    (hCC : ∀ j,C j≤C' j)
    (hnew : ∀ R hR he,CellCoordinateBounds R (extend R hR he).map C') :
    QuantitativeEndpointSkeletonCarrierMaps T m K i (n+1) C' where
  toEndpointSkeletonCarrierMaps := F.toEndpointSkeletonCarrierMaps.next extend
  coordinate_bounds R hR hr := by
    intro j z z' heq
    change dist (F.toEndpointSkeletonCarrierMaps.nextMap extend R hR hr z)
      (F.toEndpointSkeletonCarrierMaps.nextMap extend R hR hr z')≤_
    by_cases h : R.rank<n
    · simp only [EndpointSkeletonCarrierMaps.nextMap,dif_pos h]
      exact (F.coordinate_bounds R hR h j z z' heq).trans
        (mul_le_mul_of_nonneg_right (hCC j) (abs_nonneg _))
    · simp only [EndpointSkeletonCarrierMaps.nextMap,dif_neg h]
      exact hnew R hR (by omega) j z z' heq

theorem lowerFamily_update_bounds (F : QuantitativeEndpointSkeletonCarrierMaps T m K i n C)
    (R : RectangularCell d) (he : R.rank=n) (j : Fin d)
    (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
    (w : RealCoordinates d) (x y : ℝ)
    (hx : Function.update w j x∈Q.closedBox) (hy : Function.update w j y∈Q.closedBox) :
    dist ((F.toSkeletonCarrierMaps.lowerFamily R he).map Q hQ hrQ ⟨Function.update w j x,hx⟩)
      ((F.toSkeletonCarrierMaps.lowerFamily R he).map Q hQ hrQ ⟨Function.update w j y,hy⟩)≤C j*|x-y| := by
  have hh := F.coordinate_bounds Q hQ (by omega : Q.rank<n) j
    ⟨Function.update w j x,hx⟩ ⟨Function.update w j y,hy⟩ (by
      intro k hk; simp only [Function.update_of_ne hk])
  simpa using hh

end QuantitativeEndpointSkeletonCarrierMaps

namespace LowerCellCarrierMaps
variable {R : RectangularCell d}

def fillingCoordinateRate (R : RectangularCell d) (i : Fin d)
    (S B D J : ℝ≥0) (j : Fin d) : ℝ≥0 :=
  if j=i then 3*max S D/(R.transverseWidth j).toNNReal
  else 2*ControlledContraction.coneTransverseConstant S D J B/(R.transverseWidth j).toNNReal

theorem relativeCellExtension_coordinate_bounds (F : LowerCellCarrierMaps T m K i R)
    (hR : R∈T.cells) (hF : F.EndpointValues) {S B D J : ℝ≥0}
    (hi : R.lower i<R.upper i) (H : ControlledContraction (cellLeftPoint m K i R) D J)
    (hpath : ∀ v : ConeSphere (R.ActiveTransverse i→ℝ),LipschitzWith S
      (fun r => F.boundaryValue hR (prismBoundaryPoint R i v r)))
    (htrans : ∀ r : unitInterval,LipschitzWith B
      (fun v : ConeSphere (R.ActiveTransverse i→ℝ) => F.boundaryValue hR (prismBoundaryPoint R i v r))) :
    CellCoordinateBounds R (F.relativeCellExtension hR hF hi H hpath htrans).map
      (fillingCoordinateRate R i S B D J) := by
  intro j z z' heq
  by_cases hji : j=i
  · subst j
    have hw : 0<R.transverseWidth i := sub_pos.mpr (by exact_mod_cast hi)
    have hh := (F.prismBoundaryData hR hF S B hpath htrans).fill_first_dist_le H hi z z' heq
    simpa [relativeCellExtension,fillingCoordinateRate,PrismBoundaryData.continuousMap,NNReal.coe_div,NNReal.coe_mul,
      NNReal.coe_ofNat,Real.coe_toNNReal _ hw.le] using hh
  · by_cases hj : R.lower j<R.upper j
    · have hw : 0<R.transverseWidth j := sub_pos.mpr (by exact_mod_cast hj)
      have hh := (F.prismBoundaryData hR hF S B hpath htrans).fill_transverse_dist_le H hi j hji hj z z' heq
      simpa [relativeCellExtension,fillingCoordinateRate,PrismBoundaryData.continuousMap,hji,NNReal.coe_div,NNReal.coe_mul,
        NNReal.coe_ofNat,Real.coe_toNNReal _ hw.le] using hh
    · have he : R.lower j=R.upper j := le_antisymm (R.ordered j) (le_of_not_gt hj)
      have hz := R.point_eq_of_only_collapsed_coordinate j he z z' heq
      rw [hz,dist_self]
      positivity

theorem collapsedCellExtension_coordinate_bounds (F : LowerCellCarrierMaps T m K i R)
    (hR : R∈T.cells) (hF : F.EndpointValues) (hi : R.lower i=R.upper i)
    (C : Fin d→ℝ≥0) : CellCoordinateBounds R (F.collapsedCellExtension hR hF hi).map C := by
  intro j z z' heq
  change dist (cellLeftPoint m K i R) (cellLeftPoint m K i R)≤_
  rw [dist_self]
  positivity

end LowerCellCarrierMaps
end
end AbelianTargets


