-- Prove2me | Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
-- name    : AT260939824_ActualQuantitativeAtlasRecursion
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:12:11.811386+00:00
-- url     : https://prove2.me/theorems/34e63758-55c1-4f9a-b95b-40f6f4a06876
-- title:
--   Coordinate rates for quantitative atlas extension
-- statement:
--   Let $\delta_j>0$ and $U_j$ bound the positive side lengths of rectangular cells from below and above. Let $D,J\ge0$ be contraction track and joint bounds, and choose a distinguished coordinate $i$. For previous coordinate bounds $C_j$, the rank-rate sequence starts at zero and retains the maximum of the previous rate and the new filling rate. Its longitudinal filling rate is
--
--   $$ 3\max(C_iU_i,D)/\delta_i. $$
--
--   The transverse rates use the corresponding cone-extension constant. These quantities record the exact coordinate estimates required by rank induction.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 5; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/ActualQuantitativeAtlasRecursion.lean, selected declaration lines 14-15, 17-19, 21-23, 25-27, 29-52, 54-69; SHA-256 1c1cf31ee2f11df7fc2ab7c06b7ef4dbffc1861fc2c6eb4a8b16a1abe37d630d. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
import Definitions.Def_AT260939824_AtlasBoundaryTransverseBounds
import Definitions.Def_AT260939824_AtlasBoxes
import Definitions.Def_AT260939824_AtlasEndpointRecursion
import Definitions.Def_AT260939824_AtlasQuantitativeRecursion
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

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AbelianTargets
noncomputable section
open scoped NNReal BigOperators
variable {d : ℕ} {K₀ : Fin d→ℕ} {T : IntegerRectangularTiling d K₀}
variable {m K : ℕ} {i : Fin d}

def rankBoundaryRate (U C : Fin d→ℝ≥0) : ℝ≥0 :=
  2*d*(∑ j,C j*U j/2)+1

def nextRankRates (δ U C : Fin d→ℝ≥0) (D J : ℝ≥0) (i : Fin d) (j : Fin d) : ℝ≥0 :=
  max (C j) (if j=i then 3*max (C i*U i) D/δ j
    else 2*ControlledContraction.coneTransverseConstant (C i*U i) D J (rankBoundaryRate U C)/δ j)

def atlasRankRates (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (i : Fin d) : ℕ→Fin d→ℝ≥0
  | 0 => fun _ => 0
  | n+1 => nextRankRates δ U (atlasRankRates δ U D J i n) D J i

theorem atlasRankRates_step_mono (δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (i : Fin d)
    (n : ℕ) (j : Fin d) : atlasRankRates δ U D J i n j≤atlasRankRates δ U D J i (n+1) j :=
  le_max_left _ _

theorem prismTransverseBound_le_rankBoundaryRate (R : RectangularCell d) (i : Fin d)
    (C U : Fin d→ℝ≥0) (hU : ∀j,(R.transverseWidth j).toNNReal≤U j) :
    LowerCellCarrierMaps.prismTransverseBound R i C≤rankBoundaryRate U C := by
  let s : ℝ≥0 := ∑ j,C j*U j/2
  have hcard : Fintype.card (R.ActiveTransverse i)≤d := by
    have hh := Fintype.card_le_of_injective
      (Subtype.val : R.ActiveTransverse i → Fin d) Subtype.val_injective
    simpa using hh
  have hs : ∑ j : R.ActiveTransverse i,C j.val*(R.transverseWidth j.val).toNNReal/2≤
      (d : ℝ≥0)*s := by
    calc
      _ ≤ ∑ _j : R.ActiveTransverse i,s := Finset.sum_le_sum (fun j _ => by
        calc
          _ ≤ C j.val*U j.val/2 := by gcongr; exact hU j.val
          _ ≤ s := by
            change C j.val*U j.val/2≤∑ k,C k*U k/2
            exact Finset.single_le_sum (f := fun k : Fin d => C k*U k/2)
              (fun _ _ => by positivity) (Finset.mem_univ j.val))
      _ = (Fintype.card (R.ActiveTransverse i) : ℝ≥0)*s := by simp
      _ ≤ (d : ℝ≥0)*s := by gcongr
  unfold LowerCellCarrierMaps.prismTransverseBound rankBoundaryRate
  calc
    _ ≤ 2*((d : ℝ≥0)*s)+1 := by gcongr
    _ = _ := by dsimp [s]; ring

theorem fillingCoordinateRate_le_nextRankRates (R : RectangularCell d) (i : Fin d)
    (C δ U : Fin d→ℝ≥0) (D J : ℝ≥0) (hδ : ∀j,0<δ j)
    (hlower : ∀j,R.lower j<R.upper j → δ j≤(R.transverseWidth j).toNNReal)
    (hupper : ∀j,(R.transverseWidth j).toNNReal≤U j) (j : Fin d)
    (hj : R.lower j<R.upper j) :
    LowerCellCarrierMaps.fillingCoordinateRate R i (C i*(R.transverseWidth i).toNNReal)
      (LowerCellCarrierMaps.prismTransverseBound R i C) D J j≤nextRankRates δ U C D J i j := by
  have hS : C i*(R.transverseWidth i).toNNReal≤C i*U i := by gcongr; exact hupper i
  have hB := prismTransverseBound_le_rankBoundaryRate R i C U hupper
  apply le_trans _ (le_max_right _ _)
  unfold LowerCellCarrierMaps.fillingCoordinateRate
  split_ifs with hji
  · exact div_le_div₀ (by positivity) (by gcongr) (hδ j) (hlower j hj)
  · apply div_le_div₀ (by positivity) _ (hδ j) (hlower j hj)
    unfold ControlledContraction.coneTransverseConstant
    gcongr



end
end AbelianTargets


