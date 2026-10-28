-- Prove2me | solution 1 for MeasureEquivalenceL2Transport.twisted_coefficient_constant_norm_eq_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:34:18.99899+00:00
-- url     : https://prove2.me/submissions/a61f7bcb-72ae-40b9-9889-b9b4d8d5c035

import Definitions.Def_BenchmarkOperator20261026_L2FiniteOnes
import Definitions.Def_BenchmarkOperator20261026_L2LocalizedOperators
import Definitions.Def_BenchmarkOperator20261026_L2ModuleCommutant
import Definitions.Def_BenchmarkOperator20261026_L2RestrictionExtension
import Definitions.Def_BenchmarkOperator20261026_L2TransportedMatrix
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_MeasureEquivalenceL2Restriction_globalize_adjoint
import Theorems.Thm_MeasureEquivalenceL2Restriction_inner_zeroExtend_restrict

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

-- Preserved source skeleton: L2ModuleCommutant
section
/-! A bounded operator commuting with measurable multiplication
projections has an essentially bounded multiplier as its value at one.
This is a concrete L² module lemma for the finite-corner construction. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]









theorem constantVectorL2_eq_smul_one (c : ℂ) :
    constantVectorL2 μ c = c • constantOneL2 μ := by
  apply Lp.ext
  filter_upwards [constantVectorL2_coe μ c, constantOneL2_coe μ,
    Lp.coeFn_smul c (constantOneL2 μ)] with x hc h1 hsmul
  rw [hc, hsmul]
  simp [h1]

theorem indicatorConstLp_eq_indicator_one {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : ℂ) :
    indicatorConstLp 2 hs hμs c = indicatorL2 μ hs (constantVectorL2 μ c) := by
  apply Lp.ext
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c),
    indicatorL2_coe μ hs (constantVectorL2 μ c), constantVectorL2_coe μ c]
      with x hleft hright hc
  rw [hleft, hright]
  by_cases hx : x ∈ s <;> simp [hx, hc]

theorem projectionCommutant_determined_by_one (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hS : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      S (indicatorL2 μ hs f) = indicatorL2 μ hs (S f))
    (hone : T (constantOneL2 μ) = S (constantOneL2 μ)) : T = S := by
  have hfun : (T : Lp ℂ 2 μ → Lp ℂ 2 μ) = S := by
    apply Continuous.ext_on (Lp.simpleFunc.dense (by norm_num : (2 : ℝ≥0∞) ≠ ∞))
      T.continuous S.continuous
    intro f hf
    lift f to Lp.simpleFunc ℂ 2 μ using hf
    induction f using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) with
    | @indicatorConst c s hs hμs =>
      dsimp only [Lp.simpleFunc.coe_indicatorConst]
      rw [indicatorConstLp_eq_indicator_one μ hs hμs.ne c, hT, hS]
      have hc : T (constantVectorL2 μ c) = S (constantVectorL2 μ c) := by
        rw [constantVectorL2_eq_smul_one, map_smul, map_smul, hone]
      rw [hc]
    | @add f g hf hg _ ihf ihg =>
      change T ((f.toLp hf : Lp ℂ 2 μ) + (g.toLp hg : Lp ℂ 2 μ)) =
        S ((f.toLp hf : Lp ℂ 2 μ) + (g.toLp hg : Lp ℂ 2 μ))
      rw [map_add, map_add, ihf, ihg]
  exact DFunLike.coe_injective hfun



omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_coe (b : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b f =ᵐ[μ] fun x => b x * f x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) b f

omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_indicator (b : Lp ℂ ∞ μ) {s : Set α} (hs : MeasurableSet s)
    (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b (indicatorL2 μ hs f) =
      indicatorL2 μ hs (boundedMultiplierL2 μ b f) := by
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ b (indicatorL2 μ hs f),
    indicatorL2_coe μ hs f, indicatorL2_coe μ hs (boundedMultiplierL2 μ b f),
    boundedMultiplierL2_coe μ b f] with x hm hi ho hf
  rw [hm, hi, ho]
  by_cases hx : x ∈ s <;> simp [hx, hf]



theorem projectionCommutantSymbol_coe (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    projectionCommutantSymbol μ T hT =ᵐ[μ] fun x => T (constantOneL2 μ) x :=
  (projectionCommutant_value_memLp_top μ T hT).coeFn_toLp

theorem projectionCommutant_eq_multiplier (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    T = boundedMultiplierL2 μ (projectionCommutantSymbol μ T hT) := by
  apply projectionCommutant_determined_by_one μ T _ hT
    (fun _ hs f => boundedMultiplierL2_indicator μ _ hs f)
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT)
      (constantOneL2 μ), projectionCommutantSymbol_coe μ T hT, constantOneL2_coe μ]
    with x hm hs h1
  rw [hm, hs, h1, mul_one]

end MeasureUnitary

end

-- Preserved source skeleton: L2RestrictionExtension
section
/-! Actual bounded restriction and isometric zero extension for complex
L2 spaces, including their projection and adjoint identities. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

















theorem restrict_zeroExtend (A : Set X) (hA : MeasurableSet A)
    (f : Lp ℂ 2 (μ.restrict A)) : restrictMap μ A (zeroExtend μ A hA f) = f := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (zeroExtend μ A hA f),
    ae_restrict_of_ae (zeroExtend_coe μ A hA f), ae_restrict_mem hA] with x hr he hx
  rw [hr, he]
  simp only [Set.indicator_of_mem hx]

theorem zeroExtend_restrict (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 μ) :
    zeroExtend μ A hA (restrictMap μ A f) = indicatorL2 μ hA f := by
  apply Lp.ext
  have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrict_coe μ A f)
  filter_upwards [zeroExtend_coe μ A hA (restrictMap μ A f), indicatorL2_coe μ hA f, hs]
    with x he hi hsx
  exact he.trans (hsx.trans hi.symm)



theorem restrict_adjoint (A : Set X) (hA : MeasurableSet A) :
    (restrictCLM μ A).adjoint = (zeroExtendLI μ A hA).toContinuousLinearMap := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact fun f g => inner_zeroExtend_restrict μ A hA f g

theorem zeroExtend_adjoint (A : Set X) (hA : MeasurableSet A) :
    (zeroExtendLI μ A hA).toContinuousLinearMap.adjoint = restrictCLM μ A := by
  rw [← restrict_adjoint, ContinuousLinearMap.adjoint_adjoint]

end
end MeasureEquivalenceL2Restriction

end

-- Preserved source skeleton: L2LocalizedOperators
section
/-! Actual globalization and finite-measure localization of L2 module
operators, reducing a semifinite supported operator to the proved finite
measure multiplier theorem. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem restrict_indicator (A s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    restrictMap μ A (indicatorL2 μ hs f) =
      indicatorL2 (μ.restrict A) hs (restrictMap μ A f) := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (indicatorL2 μ hs f), restrict_coe μ A f,
    ae_restrict_of_ae (indicatorL2_coe μ hs f),
    indicatorL2_coe (μ.restrict A) hs (restrictMap μ A f)] with x hr hf hi ho
  rw [hr, hi, ho]
  by_cases hx : x ∈ s <;> simp [hx, hf]

theorem zeroExtend_indicator (A : Set X) (hA : MeasurableSet A)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA (indicatorL2 (μ.restrict A) hs f) =
      indicatorL2 μ hs (zeroExtend μ A hA f) := by
  apply Lp.ext
  have hsrc := (ae_eq_restrict_iff_indicator_ae_eq hA).mp
    (indicatorL2_coe (μ.restrict A) hs f)
  filter_upwards [zeroExtend_coe μ A hA (indicatorL2 (μ.restrict A) hs f),
    zeroExtend_coe μ A hA f, indicatorL2_coe μ hs (zeroExtend μ A hA f), hsrc]
    with x he hf hi hsource
  rw [he, hi, hsource]
  by_cases hxA : x ∈ A <;> by_cases hxs : x ∈ s <;> simp [hxA, hxs, hf] at *



theorem globalize_input_supported (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    globalizeOperator μ A B hB T (indicatorL2 μ hA f) = globalizeOperator μ A B hB T f := by
  change zeroExtend μ B hB (T (restrictMap μ A (indicatorL2 μ hA f))) =
    zeroExtend μ B hB (T (restrictMap μ A f))
  rw [← zeroExtend_restrict μ A hA f, restrict_zeroExtend]

theorem globalize_output_supported (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    indicatorL2 μ hB (globalizeOperator μ A B hB T f) = globalizeOperator μ A B hB T f := by
  change indicatorL2 μ hB (zeroExtend μ B hB (T (restrictMap μ A f))) =
    zeroExtend μ B hB (T (restrictMap μ A f))
  rw [← zeroExtend_restrict, restrict_zeroExtend]





theorem localize_commutes_indicator (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict C)) :
    localizeOperator μ C hC T (indicatorL2 (μ.restrict C) hs f) =
      indicatorL2 (μ.restrict C) hs (localizeOperator μ C hC T f) := by
  change restrictMap μ C (T (zeroExtend μ C hC (indicatorL2 (μ.restrict C) hs f))) =
    indicatorL2 (μ.restrict C) hs (restrictMap μ C (T (zeroExtend μ C hC f)))
  rw [zeroExtend_indicator, hT, restrict_indicator]



end
end MeasureEquivalenceL2Restriction

end

-- Preserved source skeleton: L2ProjectionCommutantNormal
section
/-! The finite-measure multiplication algebra is commutative and closed
under adjoints. In particular, a projection-commuting operator is normal.
This avoids introducing any abstract semifinite trace in the corner proof. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem inner_indicatorL2 (s : Set X) (hs : MeasurableSet s) (f g : Lp ℂ 2 μ) :
    inner ℂ (indicatorL2 μ hs f) g = inner ℂ f (indicatorL2 μ hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f, indicatorL2_coe μ hs g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx]

theorem projectionCommutant_adjoint (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T.adjoint (indicatorL2 μ hs f) = indicatorL2 μ hs (T.adjoint f) := by
  intro s hs f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_indicatorL2,
    ← hT, ← ContinuousLinearMap.adjoint_inner_right, inner_indicatorL2]

variable [IsFiniteMeasure μ]

theorem projectionCommutant_commute
    (T S : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hS : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      S (indicatorL2 μ hs f) = indicatorL2 μ hs (S f)) :
    T.comp S = S.comp T := by
  have hTm := projectionCommutant_eq_multiplier μ T hT
  have hSm := projectionCommutant_eq_multiplier μ S hS
  apply ContinuousLinearMap.ext
  intro f
  change T (S f) = S (T f)
  apply Lp.ext
  filter_upwards [boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT) (S f),
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ S hS) f,
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ S hS) (T f),
    boundedMultiplierL2_coe μ (projectionCommutantSymbol μ T hT) f]
      with x hTS hSf hST hTf
  rw [← hTm] at hTS hTf
  rw [← hSm] at hSf hST
  rw [hTS, hST, hSf, hTf]
  ring

theorem projectionCommutant_norm_adjoint
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) (f : Lp ℂ 2 μ) :
    ‖T f‖ = ‖T.adjoint f‖ := by
  have hcomm := projectionCommutant_commute μ T T.adjoint hT
    (projectionCommutant_adjoint μ T hT)
  have hnormal : IsStarNormal T := ⟨by
    change T.adjoint.comp T = T.comp T.adjoint
    exact hcomm.symm⟩
  exact (ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mp hnormal) f

end
end MeasureUnitary

end

-- Preserved source skeleton: L2LocalizedAdjoints
section
/-! Adjoint and reconstruction identities for actual finite compression.
They transfer normality of the finite multiplication algebra to the
norm comparison needed for individual semifinite matrix coefficients. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1000000

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)



theorem localize_adjoint (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    (localizeOperator μ C hC T).adjoint = localizeOperator μ C hC T.adjoint := by
  simp only [localizeOperator, ContinuousLinearMap.adjoint_comp,
    restrict_adjoint μ C hC, zeroExtend_adjoint μ C hC,
    ContinuousLinearMap.comp_assoc]

theorem supported_adjoint (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hin : ∀ f, T (indicatorL2 μ hC f) = T f)
    (hout : ∀ f, indicatorL2 μ hC (T f) = T f) :
    (∀ f, T.adjoint (indicatorL2 μ hC f) = T.adjoint f) ∧
      (∀ f, indicatorL2 μ hC (T.adjoint f) = T.adjoint f) := by
  constructor
  · intro f
    apply ext_inner_left ℂ
    intro g
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_indicatorL2, hout,
      ContinuousLinearMap.adjoint_inner_right]
  · intro f
    apply ext_inner_left ℂ
    intro g
    rw [← inner_indicatorL2, ContinuousLinearMap.adjoint_inner_right, hin,
      ContinuousLinearMap.adjoint_inner_right]

theorem zeroExtend_localize (C : Set X) (hC : MeasurableSet C)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hout : ∀ f, indicatorL2 μ hC (T f) = T f)
    (f : Lp ℂ 2 (μ.restrict C)) :
    zeroExtend μ C hC (localizeOperator μ C hC T f) = T (zeroExtend μ C hC f) := by
  change zeroExtend μ C hC (restrictMap μ C (T (zeroExtend μ C hC f))) = _
  rw [zeroExtend_restrict, hout]

theorem finite_supported_norm_adjoint (C : Set X) (hC : MeasurableSet C)
    (hfin : μ C ≠ ∞) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f))
    (hin : ∀ f, T (indicatorL2 μ hC f) = T f)
    (hout : ∀ f, indicatorL2 μ hC (T f) = T f)
    (f : Lp ℂ 2 (μ.restrict C)) :
    ‖T (zeroExtend μ C hC f)‖ = ‖T.adjoint (zeroExtend μ C hC f)‖ := by
  letI : IsFiniteMeasure (μ.restrict C) := ⟨by simpa using lt_top_iff_ne_top.mpr hfin⟩
  have hnormal := projectionCommutant_norm_adjoint (μ.restrict C)
    (localizeOperator μ C hC T) (localize_commutes_indicator μ C hC T hT) f
  rw [localize_adjoint] at hnormal
  have hout' := (supported_adjoint μ C hC T hin hout).2
  rw [← zeroExtend_localize μ C hC T hout f,
    ← zeroExtend_localize μ C hC T.adjoint hout' f,
    zeroExtend_norm, zeroExtend_norm]
  exact hnormal

end
end MeasureEquivalenceL2Restriction

end

-- Preserved source skeleton: L2FiniteOnes
section
/-! Canonical indicator vectors for finite sets, including their exact
mass, restriction and zero-extension identities. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)





theorem finiteOne_coe (A : Set X) (hA : MeasurableSet A) (hfin : μ A ≠ ∞) :
    finiteOne μ A hA hfin =ᵐ[μ] A.indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem restrictedOne_coe (A : Set X) (hfin : μ A ≠ ∞) :
    restrictedOne μ A hfin =ᵐ[μ.restrict A] fun _ => (1 : ℂ) := by
  simpa only [Set.indicator_univ] using
    (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := by simpa using hfin) (c := (1 : ℂ)))



theorem zeroExtend_restrictedOne (A : Set X) (hA : MeasurableSet A) (hfin : μ A ≠ ∞) :
    zeroExtend μ A hA (restrictedOne μ A hfin) = finiteOne μ A hA hfin := by
  apply Lp.ext
  have hc := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (restrictedOne_coe μ A hfin)
  filter_upwards [zeroExtend_coe μ A hA (restrictedOne μ A hfin),
    finiteOne_coe μ A hA hfin, hc] with x he hf hone
  exact he.trans (hone.trans hf.symm)

theorem indicatorL2_nested (A C : Set X) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hsub : A ⊆ C) (f : Lp ℂ 2 μ) :
    indicatorL2 μ hA (indicatorL2 μ hC f) = indicatorL2 μ hA f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ hA (indicatorL2 μ hC f),
    indicatorL2_coe μ hC f, indicatorL2_coe μ hA f] with x ha hc hf
  rw [ha, hf]
  by_cases hx : x ∈ A
  · simp [hx, hsub hx, hc]
  · simp [hx]

theorem indicatorL2_nested_reverse (A C : Set X) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hsub : A ⊆ C) (f : Lp ℂ 2 μ) :
    indicatorL2 μ hC (indicatorL2 μ hA f) = indicatorL2 μ hA f := by
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ hC (indicatorL2 μ hA f),
    indicatorL2_coe μ hA f] with x hc ha
  rw [hc]
  by_cases hx : x ∈ A
  · simp [hx, hsub hx]
  · by_cases hxC : x ∈ C <;> simp [hx, hxC, ha]

end
end MeasureEquivalenceL2Restriction

end

-- Preserved source skeleton: L2TransportedMatrix
section
/-! Actual transported matrix operators: Koopman transport of genuine
restricted-space coefficients gives ambient module operators supported
on the translated finite sets, and hence genuine finite-local multipliers. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Transport

open MeasureEquivalenceL2Restriction MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)



theorem pullback_coe (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (f : Lp ℂ 2 μ) :
    pullbackEquiv μ e he f =ᵐ[μ] fun x => f (e x) :=
  Lp.coeFn_compMeasurePreserving f he

theorem pullback_indicator (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    pullbackEquiv μ e he (indicatorL2 μ hs f) =
      indicatorL2 μ (hs.preimage e.measurable) (pullbackEquiv μ e he f) := by
  apply Lp.ext
  filter_upwards [pullback_coe μ e he (indicatorL2 μ hs f), pullback_coe μ e he f,
    he.quasiMeasurePreserving.ae (indicatorL2_coe μ hs f),
    indicatorL2_coe μ (hs.preimage e.measurable) (pullbackEquiv μ e he f)]
    with x hp hf hi ho
  rw [hp, hi, ho]
  by_cases hx : e x ∈ s <;> simp [hx, hf]

theorem preimage_symm_eq_image (e : X ≃ᵐ X) (A : Set X) : e.symm ⁻¹' A = e '' A := by
  ext x
  constructor
  · intro hx
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, MeasurableEquiv.symm_apply_apply] using hy

theorem measure_image (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (A : Set X) (hA : MeasurableSet A) : μ (e '' A) = μ A := by
  rw [← preimage_symm_eq_image]
  exact he.symm.measure_preimage hA.nullMeasurableSet



theorem globalize_twisted_indicator (d e : X ≃ᵐ X)
    (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    globalizeOperator μ A B hB T (indicatorL2 μ (hs.preimage e.measurable) f) =
      indicatorL2 μ (hs.preimage d.measurable) (globalizeOperator μ A B hB T f) := by
  change zeroExtend μ B hB (T (restrictMap μ A (indicatorL2 μ (hs.preimage e.measurable) f))) =
    indicatorL2 μ (hs.preimage d.measurable) (zeroExtend μ B hB (T (restrictMap μ A f)))
  rw [restrict_indicator, hT s hs, zeroExtend_indicator]

theorem transported_commutes_indicator (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f))
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    transportedOperator μ d e hd he A B hB T (indicatorL2 μ hs f) =
      indicatorL2 μ hs (transportedOperator μ d e hd he A B hB T f) := by
  change pullbackEquiv μ d.symm hd.symm
      (globalizeOperator μ A B hB T (pullbackEquiv μ e he (indicatorL2 μ hs f))) =
    indicatorL2 μ hs (pullbackEquiv μ d.symm hd.symm
      (globalizeOperator μ A B hB T (pullbackEquiv μ e he f)))
  rw [pullback_indicator, globalize_twisted_indicator μ d e A B hB T hT s hs,
    pullback_indicator]
  have hset : d.symm ⁻¹' (d ⁻¹' s) = s := by
    ext x
    simp only [mem_preimage, MeasurableEquiv.apply_symm_apply]
  simp only [hset]

theorem transported_input_supported (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    transportedOperator μ d e hd he A B hB T
      (indicatorL2 μ (e.measurableEmbedding.measurableSet_image.mpr hA) f) =
        transportedOperator μ d e hd he A B hB T f := by
  change pullbackEquiv μ d.symm hd.symm
      (globalizeOperator μ A B hB T (pullbackEquiv μ e he
        (indicatorL2 μ (e.measurableEmbedding.measurableSet_image.mpr hA) f))) =
    pullbackEquiv μ d.symm hd.symm (globalizeOperator μ A B hB T (pullbackEquiv μ e he f))
  rw [pullback_indicator]
  have hset : e ⁻¹' (e '' A) = A := Set.preimage_image_eq _ e.injective
  simp only [hset]
  rw [globalize_input_supported μ A B hA hB T]

theorem transported_output_supported (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) (f : Lp ℂ 2 μ) :
    indicatorL2 μ (d.measurableEmbedding.measurableSet_image.mpr hB)
      (transportedOperator μ d e hd he A B hB T f) =
        transportedOperator μ d e hd he A B hB T f := by
  have h := congrArg (pullbackEquiv μ d.symm hd.symm)
    (globalize_output_supported μ A B hB T (pullbackEquiv μ e he f))
  rw [pullback_indicator] at h
  simpa only [preimage_symm_eq_image] using h



end
end MeasureEquivalenceL2Transport

end

-- Preserved source skeleton: L2TransportedNorms
section
/-! The two constant-vector norms of one genuine twisted matrix
coefficient agree. The proof uses finite-support compression and the
commutative multiplication algebra, instead of postulating a trace. -/

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace

set_option maxHeartbeats 1500000

namespace MeasureEquivalenceL2Transport

open MeasureEquivalenceL2Restriction MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem pullback_symm_eq (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) :
    (pullbackEquiv μ e he).symm = pullbackEquiv μ e.symm he.symm := by
  apply LinearIsometryEquiv.ext
  intro f
  apply (pullbackEquiv μ e he).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (pullback_inverse μ μ e e.symm he he.symm
    (Eventually.of_forall (fun x => e.symm_apply_apply x)) f).symm

theorem transported_adjoint (d e : X ≃ᵐ X)
    (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    (transportedOperator μ d e hd he A B hB T).adjoint =
      transportedOperator μ e d he hd B A hA T.adjoint := by
  simp only [transportedOperator, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, pullback_symm_eq,
    globalize_adjoint μ A B hA hB, MeasurableEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

theorem restrict_pullback_finiteOne
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (A C : Set X) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hfinA : μ A ≠ ∞) (hfinC : μ C ≠ ∞) (hsub : e '' A ⊆ C) :
    restrictMap μ A (pullbackEquiv μ e he (finiteOne μ C hC hfinC)) =
      restrictedOne μ A hfinA := by
  apply Lp.ext
  filter_upwards [restrict_coe μ A (pullbackEquiv μ e he (finiteOne μ C hC hfinC)),
    ae_restrict_of_ae (pullback_coe μ e he (finiteOne μ C hC hfinC)),
    ae_restrict_of_ae (he.quasiMeasurePreserving.ae (finiteOne_coe μ C hC hfinC)),
    restrictedOne_coe μ A hfinA, ae_restrict_mem hA] with x hr hp hc hone hx
  rw [hr, hp, hc, hone]
  exact Set.indicator_of_mem (hsub (mem_image_of_mem e hx)) _

theorem transported_finiteOne_norm
    (d e : X ≃ᵐ X) (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B C : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfinA : μ A ≠ ∞) (hfinC : μ C ≠ ∞) (hsub : e '' A ⊆ C)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B)) :
    ‖transportedOperator μ d e hd he A B hB T (finiteOne μ C hC hfinC)‖ =
      ‖T (restrictedOne μ A hfinA)‖ := by
  change ‖pullbackEquiv μ d.symm hd.symm
    (zeroExtend μ B hB (T (restrictMap μ A
      (pullbackEquiv μ e he (finiteOne μ C hC hfinC)))))‖ = _
  rw [LinearIsometryEquiv.norm_map, zeroExtend_norm,
    restrict_pullback_finiteOne μ e he A C hA hC hfinA hfinC hsub]



end
end MeasureEquivalenceL2Transport

end

/-! The two constant-vector norms of one genuine twisted matrix
coefficient agree. The proof uses finite-support compression and the
commutative multiplication algebra, instead of postulating a trace. -/
open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1500000
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
open MeasureEquivalenceL2Transport
open MeasureEquivalenceL2Restriction MeasureEquivalenceEquidecomposition MeasureUnitary
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem solution
    (d e : X ≃ᵐ X) (hd : MeasurePreserving d μ μ) (he : MeasurePreserving e μ μ)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : μ A ≠ ∞) (hfinB : μ B ≠ ∞)
    (T : Lp ℂ 2 (μ.restrict A) →L[ℂ] Lp ℂ 2 (μ.restrict B))
    (hT : ∀ (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 (μ.restrict A)),
      T (indicatorL2 (μ.restrict A) (hs.preimage e.measurable) f) =
        indicatorL2 (μ.restrict B) (hs.preimage d.measurable) (T f)) :
    ‖T (restrictedOne μ A hfinA)‖ = ‖T.adjoint (restrictedOne μ B hfinB)‖ := by
  let C := e '' A ∪ d '' B
  have hEA : MeasurableSet (e '' A) := e.measurableEmbedding.measurableSet_image.mpr hA
  have hDB : MeasurableSet (d '' B) := d.measurableEmbedding.measurableSet_image.mpr hB
  have hC : MeasurableSet C := hEA.union hDB
  have hfC : μ C ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (measure_union_le _ _)
    rw [measure_image μ e he A hA, measure_image μ d hd B hB]
    exact ENNReal.add_ne_top.mpr ⟨hfinA,hfinB⟩
  let S := transportedOperator μ d e hd he A B hB T
  have hin (f : Lp ℂ 2 μ) : S (indicatorL2 μ hC f) = S f := by
    calc
      S (indicatorL2 μ hC f) = S (indicatorL2 μ hEA (indicatorL2 μ hC f)) :=
        (transported_input_supported μ d e hd he A B hA hB T _).symm
      _ = S (indicatorL2 μ hEA f) := by
        rw [indicatorL2_nested μ (e '' A) C hEA hC subset_union_left]
      _ = S f := transported_input_supported μ d e hd he A B hA hB T f
  have hout (f : Lp ℂ 2 μ) : indicatorL2 μ hC (S f) = S f := by
    calc
      indicatorL2 μ hC (S f) = indicatorL2 μ hC (indicatorL2 μ hDB (S f)) := by
        rw [transported_output_supported μ d e hd he A B hB T f]
      _ = indicatorL2 μ hDB (S f) :=
        indicatorL2_nested_reverse μ (d '' B) C hDB hC subset_union_right (S f)
      _ = S f := transported_output_supported μ d e hd he A B hB T f
  have hnorm := finite_supported_norm_adjoint μ C hC hfC S
    (transported_commutes_indicator μ d e hd he A B hB T hT) hin hout
    (restrictedOne μ C hfC)
  rw [zeroExtend_restrictedOne] at hnorm
  change ‖transportedOperator μ d e hd he A B hB T (finiteOne μ C hC hfC)‖ =
    ‖(transportedOperator μ d e hd he A B hB T).adjoint (finiteOne μ C hC hfC)‖ at hnorm
  rw [transported_adjoint μ d e hd he A B hA hB T,
    transported_finiteOne_norm μ d e hd he A B C hA hB hC hfinA hfC subset_union_left,
    transported_finiteOne_norm μ e d he hd B A C hB hA hC hfinB hfC subset_union_right] at hnorm
  exact hnorm
