-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasurePullbackMultipliers
-- name    : BenchmarkOperator20261026_MeasurePullbackMultipliers
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:43:17.784539+00:00
-- url     : https://prove2.me/theorems/ebd26456-8f66-4630-b03c-ccaf60399c1d
-- title:
--   Measure Pullback Multipliers
-- statement:
--   Defines the essentially bounded symbol obtained by pulling a continuous function back along a measurable observable, its $L^2$ multiplication operator, and the resulting star-algebra homomorphism. The retained representative, norm and algebraic identities justify these maps.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasurePullbackMultipliers.lean, lines 21–119; source SHA-256 f1a90d18d54a6c06acc41df59edad92ea7d023bb8644482d708737a93c524d0c. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
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

/-! Multiplication by pulled-back continuous functions on arbitrary
measurable measure spaces. No finiteness or topology on the source measure
space is required. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

variable {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K] [MeasurableSpace K]
  [BorelSpace K] [CompactSpace K] [SecondCountableTopology K]
  (μ : Measure Ω) (q : Ω → K) (hq : Measurable q)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

include hq

theorem pullbackContinuous_memLp_top (g : C(K, ℂ)) : MemLp (fun x => g (q x)) ∞ μ :=
  memLp_top_of_bound (g.continuous.measurable.comp hq).aestronglyMeasurable ‖g‖
    (.of_forall (fun x => g.norm_coe_le_norm (q x)))

def pullbackContinuousSymbol (g : C(K, ℂ)) : Lp ℂ ∞ μ :=
  (pullbackContinuous_memLp_top μ q hq g).toLp (fun x => g (q x))

theorem pullbackContinuousSymbol_coe (g : C(K, ℂ)) :
    pullbackContinuousSymbol μ q hq g =ᵐ[μ] fun x => g (q x) :=
  (pullbackContinuous_memLp_top μ q hq g).coeFn_toLp

theorem pullbackContinuousSymbol_norm_le (g : C(K, ℂ)) :
    ‖pullbackContinuousSymbol μ q hq g‖ ≤ ‖g‖ := by
  rw [pullbackContinuousSymbol, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg g)
  exact eLpNormEssSup_le_of_ae_bound (.of_forall (fun x => g.norm_coe_le_norm (q x)))

def pullbackContinuousSymbolCLM : C(K, ℂ) →L[ℂ] Lp ℂ ∞ μ := by
  let L : C(K, ℂ) →ₗ[ℂ] Lp ℂ ∞ μ := {
    toFun := pullbackContinuousSymbol μ q hq
    map_add' := by
      intro g h
      apply Lp.ext
      filter_upwards [pullbackContinuousSymbol_coe μ q hq (g + h),
        pullbackContinuousSymbol_coe μ q hq g, pullbackContinuousSymbol_coe μ q hq h,
        Lp.coeFn_add (pullbackContinuousSymbol μ q hq g) (pullbackContinuousSymbol μ q hq h)]
        with x hgh hg hh ha
      simp only [Pi.add_apply] at ha
      rw [hgh, ha, hg, hh]
      rfl
    map_smul' := by
      intro c g
      apply Lp.ext
      filter_upwards [pullbackContinuousSymbol_coe μ q hq (c • g), pullbackContinuousSymbol_coe μ q hq g,
        Lp.coeFn_smul c (pullbackContinuousSymbol μ q hq g)] with x hcg hg hs
      simp only [RingHom.id_apply]
      simp only [Pi.smul_apply] at hs
      rw [hcg, hs, hg]
      rfl }
  exact L.mkContinuous 1 (fun g => by simpa using pullbackContinuousSymbol_norm_le μ q hq g)

def pullbackMultiplierL2 : C(K, ℂ) →L[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) :=
  ((ContinuousLinearMap.lsmul ℂ ℂ (E := E)).holderL μ ∞ 2 2).comp
    (pullbackContinuousSymbolCLM μ q hq)

theorem pullbackMultiplierL2_coe (g : C(K, ℂ)) (f : Lp E 2 μ) :
    pullbackMultiplierL2 μ q hq g f =ᵐ[μ] fun x => g (q x) • f x := by
  have hh := (ContinuousLinearMap.lsmul ℂ ℂ (E := E)).coeFn_holder (r := 2)
    (pullbackContinuousSymbol μ q hq g) f
  filter_upwards [hh, pullbackContinuousSymbol_coe μ q hq g] with x hh hg
  exact hh.trans (by rw [hg]; rfl)

theorem pullbackMultiplierL2_one : pullbackMultiplierL2 (E := E) μ q hq (1 : C(K, ℂ)) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe μ q hq (1 : C(K, ℂ)) f] with x hx
  simpa using hx

theorem pullbackMultiplierL2_mul (g h : C(K, ℂ)) :
    pullbackMultiplierL2 (E := E) μ q hq (g * h) =
      pullbackMultiplierL2 μ q hq g * pullbackMultiplierL2 μ q hq h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe μ q hq (g * h) f,
    pullbackMultiplierL2_coe μ q hq g (pullbackMultiplierL2 μ q hq h f),
    pullbackMultiplierL2_coe μ q hq h f] with x hgh hg hh
  change (pullbackMultiplierL2 μ q hq (g * h) f) x =
    (pullbackMultiplierL2 μ q hq g (pullbackMultiplierL2 μ q hq h f)) x
  rw [hgh, hg, hh]
  exact mul_smul _ _ _

theorem pullbackMultiplierL2_algebraMap (c : ℂ) :
    pullbackMultiplierL2 (E := E) μ q hq (algebraMap ℂ C(K, ℂ) c) =
      algebraMap ℂ (Lp E 2 μ →L[ℂ] Lp E 2 μ) c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, pullbackMultiplierL2_one,
    Algebra.algebraMap_eq_smul_one]

theorem pullbackMultiplierL2_star (g : C(K, ℂ)) :
    pullbackMultiplierL2 (E := E) μ q hq (star g) = star (pullbackMultiplierL2 (E := E) μ q hq g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pullbackMultiplierL2_coe μ q hq (star g) f,
    pullbackMultiplierL2_coe μ q hq g h] with x hf hh
  rw [hf, hh]
  simp only [ContinuousMap.star_apply, inner_smul_left, inner_smul_right, starRingEnd_apply, star_star]

def pullbackMultiplierStarAlgHom : C(K, ℂ) →⋆ₐ[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun := pullbackMultiplierL2 μ q hq
  map_zero' := map_zero _
  map_one' := pullbackMultiplierL2_one μ q hq
  map_add' := map_add _
  map_mul' := pullbackMultiplierL2_mul μ q hq
  commutes' := pullbackMultiplierL2_algebraMap μ q hq
  map_star' := pullbackMultiplierL2_star μ q hq

end

end MeasureUnitary


