-- Prove2me | Definitions.Def_AT260939824_AtlasBoundaryCoordinateBounds
-- name    : AT260939824_AtlasBoundaryCoordinateBounds
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:57:38.3088+00:00
-- url     : https://prove2.me/theorems/00dc33e3-6f75-4063-890c-a6281af6dbfa
-- title:
--   Coordinate curves in a glued cell boundary
-- statement:
--   Fix a cell $R$ and compatible lower-cell carrier maps. If a coordinate line in direction $k$ remains in the boundary of $R$, its boundary-value curve is extended to all real parameters by clamping to $[R_k^-,R_k^+]$. A common lower-cell coordinate bound $C$ gives
--
--   $$ d(F(s),F(t))\le C|s-t| $$
--
--   for parameters in that interval. This retains the original coordinate constant across lower-cell seams.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/AtlasBoundaryCoordinateBounds.lean, selected declaration lines 15-20, 22-30, 32-74; SHA-256 a3f2dd66433bea10ca41f02166d4539b409e894a962fa0fd83b9c555d076cc37. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerCellGluing
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerIntervalGluing
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
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
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

/-! Coordinate estimates survive subdivisions of actual cell boundaries. -/
namespace AbelianTargets
open scoped NNReal
noncomputable section
namespace LowerCellCarrierMaps
variable {d : ℕ} {K₀ : Fin d → ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d} {R : RectangularCell d}

def boundaryCoordinateCurve (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (z : RealCoordinates d) (k : Fin d)
    (hline : ∀ r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ),Function.update z k r∈R.boundary)
    (r : ℝ) : CellIntervalCarrier m K i R :=
  F.boundaryValue hR ⟨Function.update z k (integerIntervalClamp (R.lower k) (R.upper k) r),
    hline _ (integerIntervalClamp_mem (R.ordered k) r)⟩

theorem boundaryCoordinateCurve_eq (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (z : RealCoordinates d) (k : Fin d)
    (hline : ∀ r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ),Function.update z k r∈R.boundary)
    (r : ℝ) (hr : r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ)) :
    F.boundaryCoordinateCurve hR z k hline r=F.boundaryValue hR ⟨Function.update z k r,hline r hr⟩ := by
  apply congrArg (F.boundaryValue hR)
  apply Subtype.ext
  dsimp only [boundaryCoordinateCurve]
  rw [integerIntervalClamp_eq hr]

theorem boundary_coordinate_dist_le (F : LowerCellCarrierMaps T m K i R) (hR : R∈T.cells)
    (k : Fin d) (C : ℝ≥0)
    (hcoord : ∀ (Q : RectangularCell d) (hQ : Q∈T.cells) (hrQ : Q.rank<R.rank)
      (w : RealCoordinates d) (x y : ℝ)
      (hx : Function.update w k x∈Q.closedBox) (hy : Function.update w k y∈Q.closedBox),
      dist (F.map Q hQ hrQ ⟨Function.update w k x,hx⟩)
        (F.map Q hQ hrQ ⟨Function.update w k y,hy⟩)≤C*|x-y|)
    (z : RealCoordinates d)
    (hline : ∀ r∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ),Function.update z k r∈R.boundary)
    (s t : ℝ) (hs : s∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ))
    (ht : t∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ)) :
    dist (F.boundaryValue hR ⟨Function.update z k s,hline s hs⟩)
      (F.boundaryValue hR ⟨Function.update z k t,hline t ht⟩)≤C*|s-t| := by
  let g := F.boundaryCoordinateCurve hR z k hline
  have hunit : ∀ n : ℤ,R.lower k≤n→n+1≤R.upper k→
      ∀ x∈Set.Icc (n : ℝ) ((n : ℝ)+1),∀ y∈Set.Icc (n : ℝ) ((n : ℝ)+1),
        dist (g x) (g y)≤C*|x-y| := by
    intro n hnA hnB x hx y hy
    have hlow : (R.lower k : ℝ)≤n := by exact_mod_cast hnA
    have hhigh : (n : ℝ)+1≤R.upper k := by exact_mod_cast hnB
    have hxR : x∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ) := ⟨hlow.trans hx.1,hx.2.trans hhigh⟩
    have hyR : y∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ) := ⟨hlow.trans hy.1,hy.2.trans hhigh⟩
    have hmid : ((n : ℝ)+1/2)∈Set.Icc (R.lower k : ℝ) (R.upper k : ℝ) := by constructor <;> linarith
    let w := Function.update z k ((n : ℝ)+1/2)
    let Q := T.pointCell w
    have hQ : Q∈T.cells := ⟨w,rfl⟩
    have hwR : w∈R.boundary := hline _ hmid
    have hrQ : Q.rank<R.rank := T.pointCell_rank_lt_cell_boundary hR hwR
    have hQR : Q.closedBox⊆R.closedBox := T.pointCell_subset_cell hR hwR.1
    have hwQ : w∈Q.closedBox := Q.relativeInterior_subset (T.mem_relativeInterior_pointCell w)
    have hxQ : Function.update z k x∈Q.closedBox := Q.coordinate_unit_interval z k n hwQ x hx
    have hyQ : Function.update z k y∈Q.closedBox := Q.coordinate_unit_interval z k n hwQ y hy
    change dist (F.boundaryCoordinateCurve hR z k hline x) (F.boundaryCoordinateCurve hR z k hline y)≤_
    rw [F.boundaryCoordinateCurve_eq hR z k hline x hxR,F.boundaryCoordinateCurve_eq hR z k hline y hyR]
    rw [F.boundaryValue_eq hR hQ hrQ hQR _ hxQ,F.boundaryValue_eq hR hQ hrQ hQR _ hyQ]
    rw [(cellIntervalInclude_isometry (m := m) (K := K) i hQR).dist_eq]
    exact hcoord Q hQ hrQ z x y hxQ hyQ
  have hLip := lipschitz_integer_clamped_intervals (R.lower k) (R.upper k) (R.ordered k) g C hunit
  have hh := hLip.dist_le_mul s t
  rw [integerIntervalClamp_eq hs,integerIntervalClamp_eq ht] at hh
  change dist (F.boundaryCoordinateCurve hR z k hline s) (F.boundaryCoordinateCurve hR z k hline t)≤_ at hh
  rw [F.boundaryCoordinateCurve_eq hR z k hline s hs,F.boundaryCoordinateCurve_eq hR z k hline t ht] at hh
  simpa only [Real.dist_eq] using hh

end LowerCellCarrierMaps
end
end AbelianTargets


