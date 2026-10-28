-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
-- name    : BenchmarkOperator20261026_MeasureUnitaryDensity
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:32:39.645028+00:00
-- url     : https://prove2.me/theorems/c9c29633-69ce-453a-9590-cf5af4dc1f1a
-- title:
--   Measure Unitary Density
-- statement:
--   Defines the squared-norm vector-density measure, constant $L^2$ vectors, and measurable-set multiplication projections. Their representative formulas and the square-norm integral identity are retained. These objects connect actual $L^2$ vectors with finite measures.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureUnitaryDensity.lean, lines 16–75; source SHA-256 597be580fe9c40dc13bab19adba6264878f4f8715a013c280a7547678b470311. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.L2Space
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

/-! The spectral-class measure attached to an actual L² vector, expressed
without invoking a spectral theorem. Its mass on a set is the square of the
norm of the corresponding multiplication projection. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def indicatorL2 {s : Set α} (hs : MeasurableSet s) (f : Lp E 2 μ) : Lp E 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator f)

theorem indicatorL2_coe {s : Set α} (hs : MeasurableSet s) (f : Lp E 2 μ) :
    indicatorL2 μ hs f =ᵐ[μ] s.indicator f := ((Lp.memLp f).indicator hs).coeFn_toLp

theorem l2_norm_sq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  exact real_inner_self_eq_norm_sq (f x)

noncomputable def vectorDensityMeasure (f : Lp E 2 μ) : Measure α :=
  μ.withDensity (fun x => ENNReal.ofReal (‖f x‖ ^ 2))



theorem vectorDensityMeasure_apply {s : Set α} (hs : MeasurableSet s) (f : Lp E 2 μ) :
    vectorDensityMeasure μ f s = ENNReal.ofReal (‖indicatorL2 μ hs f‖ ^ 2) := by
  apply Eq.symm
  calc
    ENNReal.ofReal (‖indicatorL2 μ hs f‖ ^ 2) =
        ∫⁻ x, ENNReal.ofReal (‖indicatorL2 μ hs f x‖ ^ 2) ∂μ := by
      rw [l2_norm_sq_integral]
      exact ofReal_integral_eq_lintegral_ofReal
        ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _))
        (.of_forall (fun x => sq_nonneg _))
    _ = ∫⁻ x in s, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr_ae
      filter_upwards [indicatorL2_coe μ hs f] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = vectorDensityMeasure μ f s := (withDensity_apply _ hs).symm

noncomputable def constantVectorL2 [IsFiniteMeasure μ] (v : E) : Lp E 2 μ :=
  (memLp_const (μ := μ) (p := 2) v).toLp (fun _ => v)

theorem constantVectorL2_coe [IsFiniteMeasure μ] (v : E) :
    constantVectorL2 μ v =ᵐ[μ] fun _ => v :=
  (memLp_const (μ := μ) (p := 2) v).coeFn_toLp



noncomputable def constantOneL2 [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  (memLp_const (μ := μ) (p := 2) (1 : ℂ)).toLp (fun _ => 1)

theorem constantOneL2_coe [IsFiniteMeasure μ] : constantOneL2 μ =ᵐ[μ] fun _ => (1 : ℂ) :=
  (memLp_const (μ := μ) (p := 2) (1 : ℂ)).coeFn_toLp



end MeasureUnitary


