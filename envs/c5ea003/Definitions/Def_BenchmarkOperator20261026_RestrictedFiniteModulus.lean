-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
-- name    : BenchmarkOperator20261026_RestrictedFiniteModulus
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:38:44.144793+00:00
-- url     : https://prove2.me/theorems/35e51c2d-879d-4045-a1ec-c4632b9b6389
-- title:
--   Restricted Finite Modulus
-- statement:
--   Defines the nonnegative real exponential scaling factor and retains the finite-product translation and scalar-measure identities that use it. These finite-dimensional formulas are used when constructing the restricted-product measure.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedFiniteModulus.lean, lines 13–53; source SHA-256 aaec3b10b0987500fc5ee6c567e8cf300c815308af096d9ee19a019a963c8632. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
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

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

variable {ι : Type*} [Fintype ι]

def expNNReal (a : ℝ) : ℝ≥0 := ⟨Real.exp a, Real.exp_nonneg a⟩

@[simp] theorem coe_expNNReal (a : ℝ) :
    (expNNReal a : ℝ≥0∞) = ENNReal.ofReal (Real.exp a) := by
  rw [ENNReal.ofReal]
  congr 1
  apply NNReal.coe_injective
  simp [expNNReal, Real.toNNReal_of_nonneg (Real.exp_nonneg a)]
  rfl

theorem pi_smul_nnreal {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    (Measure.pi fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, Measure.pi_pi]
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finsetProd,
    Finset.prod_mul_distrib]

theorem map_add_exponentialMeasure_nnreal (a : ℝ) :
    exponentialMeasure.map (fun t => t + a) = expNNReal a • exponentialMeasure := by
  rw [map_add_exponentialMeasure]
  ext s hs
  simp [Measure.smul_apply, smul_eq_mul]

theorem pi_map_add_exponentialMeasure (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => exponentialMeasure)).map (fun x i => x i + a i) =
      (expNNReal (∑ i, a i)) • Measure.pi (fun _ : ι => exponentialMeasure) := by
  letI (i : ι) : SigmaFinite (exponentialMeasure.map (fun t => t + a i)) := by
    rw [map_add_exponentialMeasure_nnreal]
    infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : ι => exponentialMeasure)
    (f := fun i t => t + a i) (fun i => (measurable_id.add_const (a i)).aemeasurable)
  dsimp only [id_eq] at hmap
  rw [hmap]
  simp_rw [map_add_exponentialMeasure_nnreal]
  rw [pi_smul_nnreal]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_prod, expNNReal, Real.exp_sum]
  rfl

end MeasureEquivalenceRestrictedProduct


