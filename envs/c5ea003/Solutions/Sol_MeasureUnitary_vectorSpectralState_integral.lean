-- Prove2me | solution 1 for MeasureUnitary.vectorSpectralState_integral
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:43:35.971004+00:00
-- url     : https://prove2.me/submissions/84a5497a-e5a7-45cf-9bde-f3d80127c10e

import Definitions.Def_BenchmarkOperator20261026_L2ModuleCommutant
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

















omit [IsFiniteMeasure μ] in
theorem boundedMultiplierL2_coe (b : Lp ℂ ∞ μ) (f : Lp ℂ 2 μ) :
    boundedMultiplierL2 μ b f =ᵐ[μ] fun x => b x * f x := by
  exact (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) b f









end MeasureUnitary

end

/-! Finite vector-state measures and faithful vectors in actual sigma-finite
L² spaces. These give measure-class reflection without postulating a spectral theorem. -/
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary
variable {Ω Λ X : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace X]

theorem solution (μ : Measure Ω) (q : Ω → X) (hq : Measurable q)
    (f : Lp ℂ 2 μ) (c : X → ℂ) (hc : Measurable c) (b : Lp ℂ ∞ μ)
    (hb : b =ᵐ[μ] fun x => c (q x)) :
    (∫ x, c x ∂vectorSpectralState μ q f) =
      inner ℂ f (boundedMultiplierL2 μ b f) := by
  rw [vectorSpectralState, integral_map hq.aemeasurable hc.aestronglyMeasurable,
    vectorDensityMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (((Lp.aestronglyMeasurable f).norm.aemeasurable.pow_const 2).ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMultiplierL2_coe μ b f,hb] with x hmul hbx
  rw [hmul,hbx]
  change (ENNReal.ofReal (‖f x‖ ^ 2)).toReal • c (q x) =
    inner ℂ (f x) (c (q x) • f x)
  rw [ENNReal.toReal_ofReal (sq_nonneg _), inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp only [Complex.real_smul, mul_comm, Complex.ofReal_pow]
  rfl
