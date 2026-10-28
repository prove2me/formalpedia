-- Prove2me | Definitions.Def_BenchmarkOperator20261026_L2ModuleCommutant
-- name    : BenchmarkOperator20261026_L2ModuleCommutant
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:34:11.92501+00:00
-- url     : https://prove2.me/theorems/46869a75-6be3-4fc9-9a8c-1e7be5a91634
-- title:
--   L2 Module Commutant
-- statement:
--   Defines multiplication by an essentially bounded complex function and the candidate multiplier symbol obtained by applying a projection-commuting operator to the constant-one vector. The retained boundedness and integrability facts justify that symbol. The resulting commutant arguments use these objects later.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization L2ModuleCommutant.lean, lines 17–135; source SHA-256 4e367c72e63e8a42c26d183453c08e8ea78b97caf8dbdb76d26eb9b54691d44b. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
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

/-! A bounded operator commuting with measurable multiplication
projections has an essentially bounded multiplier as its value at one.
This is a concrete L² module lemma for the finite-corner construction. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

theorem indicatorL2_norm_sq {s : Set α} (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖indicatorL2 μ hs f‖ ^ 2 = ∫ x in s, ‖f x‖ ^ 2 ∂μ := by
  rw [l2_norm_sq_integral, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ hs f] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem indicatorL2_one_norm_sq {s : Set α} (hs : MeasurableSet s) :
    ‖indicatorL2 μ hs (constantOneL2 μ)‖ ^ 2 = μ.real s := by
  rw [indicatorL2_norm_sq]
  calc
    (∫ x in s, ‖constantOneL2 μ x‖ ^ 2 ∂μ) = ∫ _ in s, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (constantOneL2_coe μ)] with x hx
      simp [hx]
    _ = μ.real s := by simp

theorem projectionCommutant_value_bound (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    ∀ᵐ x ∂μ, ‖T (constantOneL2 μ) x‖ ≤ ‖T‖ := by
  let u := T (constantOneL2 μ)
  have hi : Integrable (fun x => ‖u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hsq : (fun x => ‖u x‖ ^ 2) ≤ᵐ[μ] fun _ => ‖T‖ ^ 2 := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const (‖T‖ ^ 2))
    intro s hs _
    rw [← indicatorL2_norm_sq μ hs u]
    change ‖indicatorL2 μ hs (T (constantOneL2 μ))‖ ^ 2 ≤ _
    rw [← hT]
    have hn := T.le_opNorm (indicatorL2 μ hs (constantOneL2 μ))
    calc
      ‖T (indicatorL2 μ hs (constantOneL2 μ))‖ ^ 2 ≤
          (‖T‖ * ‖indicatorL2 μ hs (constantOneL2 μ)‖) ^ 2 := by
        nlinarith [norm_nonneg (T (indicatorL2 μ hs (constantOneL2 μ))),
          mul_nonneg (norm_nonneg T) (norm_nonneg (indicatorL2 μ hs (constantOneL2 μ)))]
      _ = ‖T‖ ^ 2 * μ.real s := by rw [mul_pow, indicatorL2_one_norm_sq]
      _ = ∫ _ in s, ‖T‖ ^ 2 ∂μ := by simp [mul_comm]
  filter_upwards [hsq] with x hx
  change ‖T (constantOneL2 μ) x‖ ≤ ‖T‖
  change ‖T (constantOneL2 μ) x‖ ^ 2 ≤ ‖T‖ ^ 2 at hx
  nlinarith [norm_nonneg T, norm_nonneg (T (constantOneL2 μ) x)]

theorem projectionCommutant_value_memLp_top (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) :
    MemLp (fun x => T (constantOneL2 μ) x) ∞ μ :=
  memLp_top_of_bound (Lp.aestronglyMeasurable _) ‖T‖
    (projectionCommutant_value_bound μ T hT)







omit [IsFiniteMeasure μ] in
noncomputable def boundedMultiplierL2 (b : Lp ℂ ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 b





noncomputable def projectionCommutantSymbol (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ (s : Set α) (hs : MeasurableSet s) (f : Lp ℂ 2 μ),
      T (indicatorL2 μ hs f) = indicatorL2 μ hs (T f)) : Lp ℂ ∞ μ :=
  (projectionCommutant_value_memLp_top μ T hT).toLp (fun x => T (constantOneL2 μ) x)





end MeasureUnitary


