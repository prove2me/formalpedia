-- Prove2me | Definitions.Def_AT260939824_AtlasEndpointRecursion
-- name    : AT260939824_AtlasEndpointRecursion
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:08:33.983924+00:00
-- url     : https://prove2.me/theorems/32b62b61-649a-440c-9ba1-01d22b060c5e
-- title:
--   Endpoint-preserving maps on atlas skeleta
-- statement:
--   For a rectangular tiling $T$ and rank threshold $n$, an endpoint skeleton family assigns compatible continuous carrier maps to every cell of rank less than $n$. On the two end faces of the distinguished coordinate, its values are the corresponding bottom Dirac points. A rank-$n$ extension family determines the next skeleton family while retaining these conditions.
--
--   The record and its constructors keep boundary compatibility and endpoint normalization together throughout induction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasEndpointRecursion.lean, selected declaration lines 8-13, 18-20, 22-26, 32-34, 36-57, 59-67, 69-72; SHA-256 bc005f5b0af65bccda40171ecc41658003ee37265faa2ca294a75a1ff89e3599. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
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
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

structure EndpointSkeletonCarrierMaps (T : IntegerRectangularTiling d K₀)
    (m K : ℕ) (i : Fin d) (n : ℕ) extends SkeletonCarrierMaps T m K i n where
  endpoints : ∀ (R : RectangularCell d) (hR : R∈T.cells) (hr : R.rank<n)
    (z : CellClosedDomain R),
    (z.val i=(R.lower i : ℝ) → map R hR hr z=cellLeftPoint m K i R) ∧
    (z.val i=(R.upper i : ℝ) → map R hR hr z=cellRightPoint m K i R)

namespace EndpointSkeletonCarrierMaps
variable {n : ℕ}

def empty : EndpointSkeletonCarrierMaps T m K i 0 where
  toSkeletonCarrierMaps := SkeletonCarrierMaps.empty
  endpoints R hR hr z := (Nat.not_lt_zero _ hr).elim

theorem lowerFamily_endpoints (F : EndpointSkeletonCarrierMaps T m K i n)
    (R : RectangularCell d) (he : R.rank=n) :
    (F.toSkeletonCarrierMaps.lowerFamily R he).EndpointValues := by
  intro Q hQ hr z
  exact F.endpoints Q hQ (by omega) z

variable (F : EndpointSkeletonCarrierMaps T m K i n)
variable (extend : ∀ (R : RectangularCell d) (hR : R∈T.cells) (he : R.rank=n),
  EndpointCellCarrierExtension (F.toSkeletonCarrierMaps.lowerFamily R he) hR)

def nextMap (R : RectangularCell d) (hR : R∈T.cells) (hr : R.rank<n+1) :
    C(CellClosedDomain R,CellIntervalCarrier m K i R) :=
  if h : R.rank<n then F.map R hR h else (extend R hR (by omega)).map

theorem nextMap_compatible (P Q : RectangularCell d) (hP : P∈T.cells) (hQ : Q∈T.cells)
    (hrP : P.rank<n+1) (hrQ : Q.rank<n+1) (hs : P.closedBox⊆Q.closedBox)
    (z : CellClosedDomain P) :
    cellIntervalInclude i hs (F.nextMap extend P hP hrP z)=
      F.nextMap extend Q hQ hrQ ⟨z.val,hs z.property⟩ := by
  by_cases hq : Q.rank<n
  · have hp : P.rank<n := (T.rank_le_of_cells_subset hP hQ hs).trans_lt hq
    simp only [nextMap,dif_pos hp,dif_pos hq]
    exact F.compatible P Q hP hQ hp hq hs z
  · have heq : Q.rank=n := by omega
    by_cases hp : P.rank<n
    · have hb : z.val∈Q.boundary := T.contained_cell_closed_subset_boundary hQ hP hs (by omega) z.property
      simp only [nextMap,dif_pos hp,dif_neg hq]
      rw [(extend Q hQ heq).boundary ⟨z.val,hb⟩]
      exact ((F.toSkeletonCarrierMaps.lowerFamily Q heq).boundaryValue_eq hQ hP
        (by omega) hs ⟨z.val,hb⟩ z.property).symm
    · have he : P=Q := by
        by_contra hne
        have hh := T.rank_lt_of_cells_subset_ne hP hQ hs hne
        omega
      subst P
      exact IntervalCarriers.intervalInclusion_self _

theorem nextMap_endpoints (R : RectangularCell d) (hR : R∈T.cells) (hr : R.rank<n+1)
    (z : CellClosedDomain R) :
    (z.val i=(R.lower i : ℝ) → F.nextMap extend R hR hr z=cellLeftPoint m K i R) ∧
    (z.val i=(R.upper i : ℝ) → F.nextMap extend R hR hr z=cellRightPoint m K i R) := by
  by_cases h : R.rank<n
  · simp only [nextMap,dif_pos h]
    exact F.endpoints R hR h z
  · simp only [nextMap,dif_neg h]
    exact ⟨(extend R hR (by omega)).source z,(extend R hR (by omega)).target z⟩

def next : EndpointSkeletonCarrierMaps T m K i (n+1) where
  map := F.nextMap extend
  compatible := F.nextMap_compatible extend
  endpoints := F.nextMap_endpoints extend

end EndpointSkeletonCarrierMaps
end
end AbelianTargets


