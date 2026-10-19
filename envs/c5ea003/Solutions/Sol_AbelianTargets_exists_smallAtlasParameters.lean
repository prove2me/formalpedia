-- Prove2me | solution 1 for AbelianTargets.exists_smallAtlasParameters
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:13:19.199913+00:00
-- url     : https://prove2.me/submissions/fd123e76-7f28-4342-9f58-8db301cf2436

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
import Definitions.Def_AT260939824_AtlasScaleParameters
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CanonicalIntervalContractions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierControlledContraction
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CarrierHeightDeformation
import Definitions.Def_AT260939824_CarrierIntervalInclusion
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_CommonHeightCarrierContraction
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_ContinuousAtlasPatterns
import Definitions.Def_AT260939824_ContinuousMarkerBoxes
import Definitions.Def_AT260939824_ControlledCone
import Definitions.Def_AT260939824_CovariantCuts
import Definitions.Def_AT260939824_DigitBottomCombing
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntegerGridIntervals
import Definitions.Def_AT260939824_IntegerPrismChart
import Definitions.Def_AT260939824_IntegerPrismFilling
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_NaturalLogScaleBounds
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_OrbitMarkerCuts
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_ParityCoordinates
import Definitions.Def_AT260939824_ParityFields
import Definitions.Def_AT260939824_PriorityCuts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushDirac
import Definitions.Def_AT260939824_RealizedBottomCombing
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RectangularAtlasBoundary
import Definitions.Def_AT260939824_RectangularBoundaryStrata
import Definitions.Def_AT260939824_RectangularCells
import Definitions.Def_AT260939824_RectangularCone
import Definitions.Def_AT260939824_RectangularTranslation
import Definitions.Def_AT260939824_RegularAnisotropicAtlas
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UniformCarrierContraction
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_VerticalCarrierCollapse
import Definitions.Def_AT260939824_WordPathHelpers
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
import Mathlib.Data.List.Chain
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
import Theorems.Thm_AbelianTargets_IntervalCarriers_exists_uniformCarrierContractions
import Theorems.Thm_AbelianTargets_anisotropic_rank_rates_bound
import Theorems.Thm_AbelianTargets_exists_anisotropic_scales
import Theorems.Thm_AbelianTargets_nat_log_scaled_bound

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.CanonicalIntervalContractions
section
/-! Contractions are selected once at zero-based interval widths and then
transported by an explicit isometry. The normalized data are retained as
data rather than being reselected from an existential proof at every cell. -/

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K : ℕ} {A B C D E F : ℤ}











theorem exists_normalizedContractionFamily (m : ℕ) (hm : 2≤m) (K S : ℕ)
    (hSK : Nat.log m S≤K) : ∃ J : ℝ≥0,Nonempty (NormalizedContractionFamily m K S J) := by
  classical
  obtain ⟨J,hJ⟩ := exists_uniformCarrierContractions m hm K S hSK
  exact ⟨J,⟨fun R hR hRS=>Classical.choice (hJ R hR hRS)⟩⟩







end
end AbelianTargets.IntervalCarriers

namespace AbelianTargets.ControlledContraction
open scoped NNReal unitInterval
noncomputable section
variable {Z : Type*} [MetricSpace Z] {p q : Z} {D J : ℝ≥0}





end
end AbelianTargets.ControlledContraction

namespace AbelianTargets.IntervalCarriers
open scoped unitInterval NNReal
noncomputable section
variable {m K S : ℕ} {J : ℝ≥0}





end
end AbelianTargets.IntervalCarriers

end

-- Preserved source skeleton: AbelianTargets.ControlledAtlasScaleChoice
section
namespace AbelianTargets
noncomputable section
open scoped NNReal

theorem uniformCarrierSpeed_log_bound (m : ℕ) (hm : 2≤m) (L : ℕ) :
    (IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)≤
      (2*(3*m+8 : ℕ) : ℝ)*carrierHeightLogCoefficient m 6*Real.log ((L : ℝ)+2) := by
  have hh := nat_log_scaled_bound m hm 6 (by norm_num) L
  have he : (IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)=
      (2*(3*m+8 : ℕ) : ℝ)*(Nat.log m (6*(L+2))+1 : ℝ) := by
    unfold IntervalCarriers.uniformCarrierSpeed
    push_cast
    ring
  rw [he]
  calc
    _ ≤ (2*(3*m+8 : ℕ) : ℝ)*(carrierHeightLogCoefficient m 6*Real.log ((L : ℝ)+2)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem exists_controlled_atlas_scales (m : ℕ) (hm : 2≤m)
    (A : ℝ≥0) (B : ℕ→ℝ) (L₀ M₀ : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃L M : ℕ,1≤L ∧ L₀≤L ∧ 1≤M ∧ M₀≤M ∧
      (A : ℝ)*(IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)/(L : ℝ)+B L/(M : ℝ)<ε := by
  obtain ⟨L,M,hL,hL₀,hM,hM₀,hh⟩ := exists_anisotropic_scales
    ((A : ℝ)*(2*(3*m+8 : ℕ) : ℝ)*carrierHeightLogCoefficient m 6) B L₀ M₀ hε
  refine ⟨L,M,hL,hL₀,hM,hM₀,lt_of_le_of_lt ?_ hh⟩
  have hs := uniformCarrierSpeed_log_bound m hm L
  have ha : (A : ℝ)* (IntervalCarriers.uniformCarrierSpeed m (Nat.log m (6*(L+2))) : ℝ)≤
      ((A : ℝ)*(2*(3*m+8 : ℕ) : ℝ)*carrierHeightLogCoefficient m 6)*Real.log ((L : ℝ)+2) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs A.coe_nonneg
  exact add_le_add (div_le_div_of_nonneg_right ha (by positivity : 0≤(L : ℝ))) le_rfl

end
end AbelianTargets

end

/-!
Choose the longitudinal scale before the transverse scale. The common
contraction family and its joint constant depend only on the former.
This produces the literal rank rates needed by the canonical marker atlas.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal

theorem solution (m : ℕ) (hm : 2 ≤ m) (d : ℕ)
    (i : Fin d) {η : ℝ} (hη : 0 < η) :
    Nonempty (SmallAtlasParameters m d i η) := by
  classical
  let K : ℕ → ℕ := fun a => Nat.log m (6 * (a + 2))
  let D : ℕ → ℝ≥0 := fun a => IntervalCarriers.uniformCarrierSpeed m (K a)
  have hfamily (a : ℕ) : ∃ J : ℝ≥0,
      Nonempty (IntervalCarriers.NormalizedContractionFamily m (K a) (6 * a) J) := by
    apply IntervalCarriers.exists_normalizedContractionFamily m hm (K a) (6 * a)
    exact Nat.log_mono_right (by omega)
  choose J hJ using hfamily
  let H (a : ℕ) := Classical.choice (hJ a)
  let P : ℝ≥0 := (61 ^ d : ℕ)
  let A : ℝ≥0 := firstRankFactor P (d + 1)
  let B : ℕ → ℝ := fun a => (transverseRankFactor P d (D a) (J a) (d + 1) : ℝ)
  obtain ⟨a, b, ha, ha₀, hb, hb₀, hsmall⟩ :=
    exists_controlled_atlas_scales m hm A B (32 * 61 ^ d) (32 * 61 ^ d) hη
  let L : Fin d → ℕ := fun j => if j = i then a else b
  have hLi : L i = a := by simp [L]
  have hpos : ∀ j, 1 ≤ L j := by
    intro j
    dsimp [L]
    split_ifs <;> assumption
  have hlarge : ∀ j, 32 * 61 ^ d ≤ L j := by
    intro j
    dsimp [L]
    split_ifs <;> assumption
  have hP : 0 < P := by dsimp [P]; positivity
  have hfirst : (A : ℝ) * (D a : ℝ) / (a : ℝ) < η := by
    have hnonneg : 0 ≤ B a / (b : ℝ) := by dsimp [B]; positivity
    change (A : ℝ) * (D a : ℝ) / (a : ℝ) + B a / (b : ℝ) < η at hsmall
    linarith
  have hother : B a / (b : ℝ) < η := by
    have hnonneg : 0 ≤ (A : ℝ) * (D a : ℝ) / (a : ℝ) := by positivity
    change (A : ℝ) * (D a : ℝ) / (a : ℝ) + B a / (b : ℝ) < η at hsmall
    linarith
  refine ⟨{
    scales := L
    scales_pos := hpos
    scales_large := hlarge
    height := K a
    joint := J a
    contractions := by simpa only [hLi] using H a
    rate_lt := ?_
  }⟩
  intro j
  have hlower : (fun k => (L k : ℝ≥0) / (32 * (61 ^ d : ℕ))) =
      anisotropicLowerRates i P (a : ℝ≥0) (b : ℝ≥0) := by
    funext k
    dsimp [L, anisotropicLowerRates, P]
    split_ifs <;> rfl
  have hupper : (fun k => 6 * (L k : ℝ≥0)) =
      anisotropicUpperRates i (a : ℝ≥0) (b : ℝ≥0) := by
    funext k
    dsimp [L, anisotropicUpperRates]
    split_ifs <;> rfl
  rw [hlower, hupper]
  have hrates := anisotropic_rank_rates_bound i P (a : ℝ≥0) (b : ℝ≥0)
    (D a) (J a) hP (by exact_mod_cast ha) (by exact_mod_cast hb) (d + 1) j
  have hrates' :
      (atlasRankRates (anisotropicLowerRates i P (a : ℝ≥0) (b : ℝ≥0))
        (anisotropicUpperRates i (a : ℝ≥0) (b : ℝ≥0))
        (D a) (J a) i (d + 1) j : ℝ) ≤
      (if j = i then A * D a / (a : ℝ≥0)
        else transverseRankFactor P d (D a) (J a) (d + 1) / (b : ℝ≥0) : ℝ≥0) := by
    exact_mod_cast hrates
  apply lt_of_le_of_lt hrates'
  by_cases hj : j = i
  · simpa only [if_pos hj, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast] using hfirst
  · simpa only [if_neg hj, NNReal.coe_div, NNReal.coe_natCast, B] using hother
