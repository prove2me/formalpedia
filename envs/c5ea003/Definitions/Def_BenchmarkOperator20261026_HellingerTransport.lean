-- Prove2me | Definitions.Def_BenchmarkOperator20261026_HellingerTransport
-- name    : BenchmarkOperator20261026_HellingerTransport
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:26:00.040911+00:00
-- url     : https://prove2.me/theorems/f217ce06-3982-407c-a84f-b9f7a34e47d6
-- title:
--   Hellinger Transport
-- statement:
--   Defines square-root Radon–Nikodym vectors and the corresponding squared Hellinger energy relative to a reference measure. The retained facts give membership in $L^2$, the representative formula, nonnegativity, and the root norm. Change-of-reference and transport theorems use these objects later.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization HellingerTransport.lean, lines 11–127; source SHA-256 aebe47b1dae35755a8fd7d184ecf358eaa4b24986823d5e276f7ac2ce4923d17. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Tactic

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

open MeasureTheory Filter

namespace MeasureEquivalenceHellinger

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Squared Hellinger energy calculated with a specified reference measure. -/
noncomputable def energy (μ ν ρ : Measure α) : ℝ :=
  ∫ x, (Real.sqrt (μ.rnDeriv ρ x).toReal -
    Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2 ∂ρ











theorem sqrt_rnDeriv_memLp (μ ρ : Measure α) [IsFiniteMeasure μ] :
    MemLp (fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal) 2 ρ := by
  apply (memLp_two_iff_integrable_sq
    ((Measure.measurable_rnDeriv μ ρ).ennreal_toReal.sqrt.aestronglyMeasurable)).2
  have hi := Measure.integrableOn_toReal_rnDeriv (ν := ρ) (measure_ne_top μ Set.univ)
  simpa only [IntegrableOn, Measure.restrict_univ, Real.sq_sqrt ENNReal.toReal_nonneg]
    using hi

/-- The actual L² class of the nonnegative square root of a finite measure's RN density. -/
noncomputable def root (μ ρ : Measure α) [IsFiniteMeasure μ] : Lp ℝ 2 ρ :=
  (sqrt_rnDeriv_memLp μ ρ).toLp (fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal)

theorem root_coe (μ ρ : Measure α) [IsFiniteMeasure μ] :
    root μ ρ =ᵐ[ρ] fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal :=
  (sqrt_rnDeriv_memLp μ ρ).coeFn_toLp





theorem root_nonnegative (μ ρ : Measure α) [IsFiniteMeasure μ] :
    0 ≤ root μ ρ := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [root_coe μ ρ] with x hx
  rw [hx]
  exact Real.sqrt_nonneg _

theorem root_norm_sq (μ ρ : Measure α) [IsFiniteMeasure μ] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) : ‖root μ ρ‖ ^ 2 = μ.real Set.univ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    ← Measure.integral_toReal_rnDeriv hμ]
  apply integral_congr_ae
  filter_upwards [root_coe μ ρ] with x hx
  rw [hx]
  simp [Real.sq_sqrt ENNReal.toReal_nonneg]

theorem root_probability_norm (μ ρ : Measure α) [IsProbabilityMeasure μ] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) : ‖root μ ρ‖ = 1 := by
  have h := root_norm_sq μ ρ hμ
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at h
  nlinarith [norm_nonneg (root μ ρ)]



end MeasureEquivalenceHellinger


