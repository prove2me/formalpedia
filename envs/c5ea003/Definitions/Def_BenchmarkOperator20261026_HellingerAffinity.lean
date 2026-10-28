-- Prove2me | Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
-- name    : BenchmarkOperator20261026_HellingerAffinity
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:28:09.246807+00:00
-- url     : https://prove2.me/theorems/30103fce-167e-459d-a820-add3d3fdcbd0
-- title:
--   Hellinger Affinity
-- statement:
--   Defines Hellinger affinity of finite measures, both with a specified dominating reference and with the sum of the measures as reference. The retained integral and reference-comparison identities connect these definitions. Probability bounds and the singularity criterion are separate theorem nodes.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization HellingerAffinity.lean, lines 16–77; source SHA-256 83c020c5fcf38ac35d98560bbea05154c302df3cd72b637268039abe9b43afa2. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
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

/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Y : Type*} [MeasurableSpace Y]

/-- Hellinger affinity, using the canonical dominating measure `μ + ν`. -/
noncomputable def affinity (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ :=
  inner ℝ (root μ (μ + ν)) (root ν (μ + ν))

/-- The same RN integral with an explicit dominating reference measure. -/
noncomputable def affinityAgainst (μ ν ρ : Measure Y) : ℝ :=
  ∫ y, Real.sqrt (μ.rnDeriv ρ y).toReal * Real.sqrt (ν.rnDeriv ρ y).toReal ∂ρ

theorem affinity_integral (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    affinity μ ν = ∫ y, Real.sqrt (μ.rnDeriv (μ + ν) y).toReal *
      Real.sqrt (ν.rnDeriv (μ + ν) y).toReal ∂(μ + ν) := by
  rw [affinity, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [root_coe μ (μ + ν), root_coe ν (μ + ν)] with y hμ hν
  rw [hμ, hν]
  simp [mul_comm]





/-- Change of dominating measure for the actual affinity RN integral. -/
theorem affinityAgainst_change_reference (μ ν ρ σ : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    affinityAgainst μ ν σ = affinityAgainst μ ν ρ := by
  unfold affinityAgainst
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with y hmy hny
  simp only [Pi.mul_apply] at hmy hny
  rw [← hmy, ← hny, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_mul ENNReal.toReal_nonneg]
  calc
    _ = (Real.sqrt (ρ.rnDeriv σ y).toReal) ^ 2 *
        (Real.sqrt (μ.rnDeriv ρ y).toReal * Real.sqrt (ν.rnDeriv ρ y).toReal) := by ring
    _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]

/-- Any sigma-finite common dominating measure computes the same affinity. -/
theorem affinity_eq_affinityAgainst (μ ν ρ : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) :
    affinity μ ν = affinityAgainst μ ν ρ := by
  rw [affinity_integral]
  change affinityAgainst μ ν (μ + ν) = affinityAgainst μ ν ρ
  exact (affinityAgainst_change_reference μ ν (μ + ν) ρ
    (Measure.AbsolutelyContinuous.rfl.add_right ν)
    (Measure.AbsolutelyContinuous.rfl.add_right' μ)
    (Measure.AbsolutelyContinuous.add_left hμ hν)).symm







end MeasureEquivalenceHellinger


