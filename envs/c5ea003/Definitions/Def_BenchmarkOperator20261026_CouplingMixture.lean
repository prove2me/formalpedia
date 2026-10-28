-- Prove2me | Definitions.Def_BenchmarkOperator20261026_CouplingMixture
-- name    : BenchmarkOperator20261026_CouplingMixture
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:27:42.156811+00:00
-- url     : https://prove2.me/theorems/21d6b0e2-cfa8-4f13-8935-8995784e0881
-- title:
--   Coupling Mixture
-- statement:
--   Defines positive geometric weights, countable mixtures of couplings, and the normalized Metropolis mixture coupling and transition. The weight sum and marginal identities required for normalization are retained. The later fixed-space argument uses this common transition.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization CouplingMixture.lean, lines 15–132; source SHA-256 edd6f79b7073cda4848de3b6b14b508788c748ef70d265674d8cb1f4136f8057. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
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

/-! Countably many accepted couplings are combined into one contraction.
Positive weights retain precisely the intersection of all fixed spaces. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

noncomputable def couplingMixture (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z)) :
    Measure (Z × Z) := Measure.sum (fun n => w n • J n)

theorem couplingMixture_marginal_fst (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z))
    (μ : Measure Z) (hw : ∑' n, w n = 1) (hJ : ∀ n, (J n).map Prod.fst = μ) :
    (couplingMixture w J).map Prod.fst = μ := by
  rw [couplingMixture, Measure.map_sum measurable_fst.aemeasurable]
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp_rw [Measure.map_smul, hJ, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right, hw, one_mul]

theorem couplingMixture_marginal_snd (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z))
    (μ : Measure Z) (hw : ∑' n, w n = 1) (hJ : ∀ n, (J n).map Prod.snd = μ) :
    (couplingMixture w J).map Prod.snd = μ := by
  rw [couplingMixture, Measure.map_sum measurable_snd.aemeasurable]
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp_rw [Measure.map_smul, hJ, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right, hw, one_mul]



/-- A concrete strictly positive probability vector. -/
noncomputable def geometricWeights (n : ℕ) : ℝ≥0∞ := (2⁻¹) ^ (n + 1)



theorem geometricWeights_sum : ∑' n, geometricWeights n = 1 := by
  unfold geometricWeights
  rw [ENNReal.tsum_geometric_add_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)



/-- One explicit stationary coupling carries all countably many
accepted automorphism moves with strictly positive geometric weights. -/
noncomputable def metropolisMixtureCoupling (μ : Measure Z) (e : ℕ → Z ≃ᵐ Z) :
    Measure (Z × Z) :=
  couplingMixture geometricWeights (fun n => completedCoupling μ (acceptanceFlow μ (e n)) (e n))

theorem metropolisMixtureCoupling_marginals (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    (metropolisMixtureCoupling μ e).map Prod.fst = μ + μ ∧
      (metropolisMixtureCoupling μ e).map Prod.snd = μ + μ := by
  constructor
  · apply couplingMixture_marginal_fst _ _ _ geometricWeights_sum
    intro n
    exact (completedCoupling_marginals μ _ (e n)
      (acceptanceFlow_le μ (e n)) (acceptanceFlow_inverse_le μ (e n) (hmap n))).1
  · apply couplingMixture_marginal_snd _ _ _ geometricWeights_sum
    intro n
    exact (completedCoupling_marginals μ _ (e n)
      (acceptanceFlow_le μ (e n)) (acceptanceFlow_inverse_le μ (e n) (hmap n))).2







/-- Normalized version with the original probability/finite measure μ
as each marginal. -/
noncomputable def normalizedMetropolisCoupling (μ : Measure Z) (e : ℕ → Z ≃ᵐ Z) :
    Measure (Z × Z) := (2 : ℝ≥0∞)⁻¹ • metropolisMixtureCoupling μ e

theorem half_smul_double (μ : Measure Z) : (2 : ℝ≥0∞)⁻¹ • (μ + μ) = μ := by
  rw [← two_smul ℝ≥0∞ μ, smul_smul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

theorem normalizedMetropolisCoupling_marginals (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    (normalizedMetropolisCoupling μ e).map Prod.fst = μ ∧
      (normalizedMetropolisCoupling μ e).map Prod.snd = μ := by
  constructor
  · rw [normalizedMetropolisCoupling, Measure.map_smul,
      (metropolisMixtureCoupling_marginals μ e hmap).1, half_smul_double]
  · rw [normalizedMetropolisCoupling, Measure.map_smul,
      (metropolisMixtureCoupling_marginals μ e hmap).2, half_smul_double]

noncomputable def normalizedMetropolisTransition (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  couplingTransition μ (normalizedMetropolisCoupling μ e)
    (normalizedMetropolisCoupling_marginals μ e hmap).1
    (normalizedMetropolisCoupling_marginals μ e hmap).2





end MeasureEquivalenceMarkov


