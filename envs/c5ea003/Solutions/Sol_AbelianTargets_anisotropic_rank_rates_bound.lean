-- Prove2me | solution 1 for AbelianTargets.anisotropic_rank_rates_bound
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:10:18.995314+00:00
-- url     : https://prove2.me/submissions/292cc1e6-c15d-4298-b8fe-3fe998b8e3b3

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ActualQuantitativeAtlasRecursion
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_AnisotropicRankRates
import Definitions.Def_AT260939824_AtlasBoundaryCarrierMaps
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
end AbelianTargets
open AbelianTargets
open scoped NNReal BigOperators

theorem solution {d : ℕ} (i : Fin d) (P L M D J : ℝ≥0)
    (hP : 0<P) (hL : 0<L) (hM : 0<M) (n : ℕ) :
    ∀ j,atlasRankRates (anisotropicLowerRates i P L M) (anisotropicUpperRates i L M) D J i n j≤
      if j=i then firstRankFactor P n*D/L else transverseRankFactor P d D J n/M := by
  induction n with
  | zero => intro j; simp [atlasRankRates,firstRankFactor,transverseRankFactor]
  | succ n ih =>
    let C := atlasRankRates (anisotropicLowerRates i P L M) (anisotropicUpperRates i L M) D J i n
    let A := firstRankFactor P n
    let B := transverseRankFactor P d D J n
    have hS : C i*anisotropicUpperRates i L M i≤6*A*D := by
      have hi := ih i
      simp at hi
      calc
        _ = C i*(6*L) := by simp [anisotropicUpperRates]
        _ ≤ (A*D/L)*(6*L) := mul_le_mul_right' hi _
        _ = _ := by field_simp <;> ring
    have hB : rankBoundaryRate (anisotropicUpperRates i L M) C≤6*d*d*(A*D+B)+1 := by
      have hterm : ∀j,C j*anisotropicUpperRates i L M j/2≤3*(A*D+B) := by
        intro j
        have hc := ih j
        by_cases hj : j=i
        · subst j
          calc
            _ ≤ 6*A*D/2 := by gcongr
            _ ≤ _ := by
              rw [show 6*A*D/2=3*(A*D) by ring]
              exact mul_le_mul_left' (le_add_of_nonneg_right (by positivity)) 3
        · simp only [if_neg hj] at hc
          calc
            _ = C j*(6*M)/2 := by simp [anisotropicUpperRates,hj]
            _ ≤ (B/M)*(6*M)/2 := by gcongr
            _ = 3*B := by field_simp <;> ring
            _ ≤ _ := mul_le_mul_left' (le_add_of_nonneg_left (by positivity : 0≤A*D)) 3
      have hs : (∑ j,C j*anisotropicUpperRates i L M j/2)≤(d : ℝ≥0)*(3*(A*D+B)) := by
        calc
          _ ≤ ∑ _j : Fin d,3*(A*D+B) := Finset.sum_le_sum (fun j _ => hterm j)
          _ = _ := by simp
      unfold rankBoundaryRate
      calc
        _ ≤ 2*d*((d : ℝ≥0)*(3*(A*D+B)))+1 := by gcongr
        _ = _ := by ring
    intro j
    change nextRankRates (anisotropicLowerRates i P L M) (anisotropicUpperRates i L M) C D J i j≤_
    unfold nextRankRates
    by_cases hj : j=i
    · subst j
      simp only [if_true]
      apply max_le
      · have hci : C i≤A*D/L := by simpa [C,A] using ih i
        exact hci.trans (by dsimp [firstRankFactor]; gcongr; exact le_max_left _ _)
      · have hmax : max (C i*anisotropicUpperRates i L M i) D≤max (6*A) 1*D := by
          apply max_le
          · exact hS.trans (by gcongr; exact le_max_left _ _)
          · simpa only [one_mul] using (mul_le_mul_right' (le_max_right (6*A) 1) D)
        calc
          _ ≤ (3*(max (6*A) 1*D))/(L/(32*P)) := by
            unfold anisotropicLowerRates
            simp only [if_true]
            exact div_le_div₀ (by positivity) (mul_le_mul_left' hmax 3) (by positivity) le_rfl
          _ = (96*P*max (6*A) 1)*D/L := by field_simp <;> ring
          _ ≤ _ := by dsimp [firstRankFactor]; gcongr; exact le_max_right _ _
    · simp only [if_neg hj]
      apply max_le
      · exact (ih j).trans (by simp only [if_neg hj]; dsimp [transverseRankFactor]; gcongr; exact le_max_left _ _)
      · have hcone : ControlledContraction.coneTransverseConstant (C i*anisotropicUpperRates i L M i) D J
            (rankBoundaryRate (anisotropicUpperRates i L M) C)≤
          ControlledContraction.coneTransverseConstant (6*A*D) D J (6*d*d*(A*D+B)+1) := by
          unfold ControlledContraction.coneTransverseConstant
          gcongr
        calc
          _ ≤ (2*ControlledContraction.coneTransverseConstant (6*A*D) D J (6*d*d*(A*D+B)+1))/(M/(32*P)) := by
            unfold anisotropicLowerRates
            simp only [if_neg hj]
            gcongr
          _ = (64*P*ControlledContraction.coneTransverseConstant (6*A*D) D J (6*d*d*(A*D+B)+1))/M := by
            field_simp <;> ring
          _ ≤ _ := by dsimp [transverseRankFactor]; gcongr; exact le_max_right _ _
