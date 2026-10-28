-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
-- name    : BenchmarkOperator20261026_MeasureL2Constants
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:34:44.54269+00:00
-- url     : https://prove2.me/theorems/052011df-2de1-4b25-b3b7-e2c2a47e5757
-- title:
--   Measure L2 Constants
-- statement:
--   Defines the isometric embedding of a coefficient Hilbert space into the Hilbert-valued $L^2$ space of a probability measure by constant functions. The retained norm and linear-independence facts give the non-finite-dimensional instances needed by the amplified construction.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureL2Constants.lean, lines 18–75; source SHA-256 734b905fb0897520cdee55ffdc7722148f607d5ee45e133b6d9b219a53356f39. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

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

/-! A genuine isometric copy of the coefficient Hilbert space inside
Hilbert-valued L² of a probability measure. This proves that the amplified
Cantor representation has infinite-dimensional fibers, including at atoms. -/

open MeasureTheory Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem constantVectorL2_norm (v : E) : ‖constantVectorL2 μ v‖ = ‖v‖ := by
  rw [constantVectorL2, Lp.norm_toLp,
    eLpNorm_const' v (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  simp

noncomputable def constantVectorLI : E →ₗᵢ[ℂ] Lp E 2 μ where
  toFun := constantVectorL2 μ
  map_add' := by
    intro v w
    apply Lp.ext
    filter_upwards [constantVectorL2_coe μ (v + w), constantVectorL2_coe μ v,
      constantVectorL2_coe μ w, Lp.coeFn_add (constantVectorL2 μ v) (constantVectorL2 μ w)]
      with x hvw hv hw ha
    simp only [Pi.add_apply] at ha
    rw [hvw, ha, hv, hw]
  map_smul' := by
    intro c v
    apply Lp.ext
    filter_upwards [constantVectorL2_coe μ (c • v), constantVectorL2_coe μ v,
      Lp.coeFn_smul c (constantVectorL2 μ v)] with x hcv hv hs
    simp only [Pi.smul_apply] at hs
    simp only [RingHom.id_apply]
    rw [hcv, hs, hv]
  norm_map' := constantVectorL2_norm μ

theorem constantVectorL2_linearIndependent {ι : Type*} {v : ι → E}
    (hv : LinearIndependent ℂ v) :
    LinearIndependent ℂ (fun i => constantVectorL2 μ (v i)) :=
  hv.map' (constantVectorLI μ).toLinearMap
    (LinearMap.ker_eq_bot.mpr (constantVectorLI μ).injective)

theorem canonicalHilbert_single_linearIndependent :
    LinearIndependent ℂ (fun i : ℕ => (lp.single 2 i (1 : ℂ) : OperatorCoding.CanonicalHilbert)) := by
  let b : HilbertBasis ℕ ℂ OperatorCoding.CanonicalHilbert :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : (fun i => b i) = fun i => (lp.single 2 i (1 : ℂ) : OperatorCoding.CanonicalHilbert) := by
    funext i
    rw [← b.repr_symm_single]
    rfl
  rw [← hb]
  exact b.orthonormal.linearIndependent

theorem amplifiedL2_not_finiteDimensional :
    ¬ FiniteDimensional ℂ (Lp OperatorCoding.CanonicalHilbert 2 μ) := by
  intro h
  letI := h
  have hi := constantVectorL2_linearIndependent μ canonicalHilbert_single_linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite _ hi

instance cantor_countablyGenerated : MeasurableSpace.CountablyGenerated CantorSpace where
  isCountablyGenerated :=
    ⟨Set.range cantorCylinder, Set.countable_range _, cantorCylinder_generates.symm⟩

instance amplifiedL2_secondCountable (ν : Measure CantorSpace) [SFinite ν] :
    SecondCountableTopology (Lp OperatorCoding.CanonicalHilbert 2 ν) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  infer_instance

end MeasureUnitary


