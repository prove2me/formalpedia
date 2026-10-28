-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedSupport
-- name    : BenchmarkOperator20261026_RestrictedSupport
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:46:59.606231+00:00
-- url     : https://prove2.me/theorems/4dd297aa-957f-48d2-8346-c07f1cf9f296
-- title:
--   Restricted Support
-- statement:
--   Retains the almost-everywhere carrier membership and complementary null-set identities for shifted tail, stage and restricted-product measures under their stated summability hypotheses. These support facts are used when evaluating summable translations on the restricted-product carrier.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedSupport.lean, lines 13–95; source SHA-256 7b396a774c98fe0653e18f8480ec88b8dcca75aace53437289bc3c31b6594e69. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedDeparture
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Rat

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
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

theorem tsum_departureProbability_ne_top (h : ℕ → ℝ)
    (hh : Summable (fun n => |h n|)) : (∑' n, departureProbability (h n)) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum (fun n => departureProbability_le (h n)))
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top (by norm_num) hh.tsum_ofReal_ne_top



theorem ae_shift_mem_tailProbability (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    ∀ᵐ x ∂tailProbability, x + h ∈ restrictedProductSpace := by
  let A : ℕ → Set RealSequences := fun n => {x | x n ∈ departureSet (h n)}
  have hA (n : ℕ) : tailProbability (A n) = departureProbability (h n) := by
    have hm : tailProbability.map (fun x => x n) = baseMeasure :=
      Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) n
    change tailProbability ((fun x : RealSequences => x n) ⁻¹' departureSet (h n)) = _
    rw [← Measure.map_apply (measurable_pi_apply n) (measurable_departureSet (h n)), hm]
    rfl
  have hsum : (∑' n, tailProbability (A n)) ≠ ∞ := by
    simp_rw [hA]
    exact tsum_departureProbability_ne_top h hh
  filter_upwards [ae_eventually_notMem hsum, ae_base_tailProbability] with x hx hi
  obtain ⟨N, hN⟩ := eventually_atTop.mp hx
  apply mem_iUnion.mpr
  refine ⟨N, ?_⟩
  intro n hn
  have hnot : ¬ (x n ∈ baseInterval ∧ x n + h n ∉ baseInterval) := hN n hn
  exact not_not.mp (fun hbad => hnot ⟨hi n, hbad⟩)

theorem ae_shift_mem_stageMeasure (h : RealSequences)
    (hh : Summable (fun n => |h n|)) (n : ℕ) :
    ∀ᵐ x ∂stageMeasure n, x + h ∈ restrictedProductSpace := by
  let t : RealSequences := fun k => h (n + k)
  have ht : Summable (fun k => |t k|) :=
    hh.comp_injective (by intro i j hij; exact Nat.add_left_cancel hij)
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    ((measurable_id.add_const h) measurable_restrictedProductSpace)).mpr
  apply (Measure.ae_prod_iff_ae_ae
    (((measurable_id.add_const h).comp (headTailEquiv n).symm.measurable)
      measurable_restrictedProductSpace)).mpr
  apply ae_of_all
  intro head
  filter_upwards [ae_shift_mem_tailProbability t ht] with tail htail
  obtain ⟨M, hM⟩ := mem_iUnion.mp htail
  apply mem_iUnion.mpr
  refine ⟨n + M, ?_⟩
  intro k hk
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ k)
  have hr : M ≤ r := by omega
  simpa only [Function.comp_apply, id_eq, Pi.add_apply, headTailEquiv_symm_tail, t] using hM r hr

theorem ae_shift_mem_restrictedProductMeasure (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    ∀ᵐ x ∂restrictedProductMeasure, x + h ∈ restrictedProductSpace := by
  rw [ae_iff]
  change restrictedProductStages.limit {x | x + h ∉ restrictedProductSpace} = 0
  have hbad : MeasurableSet {x : RealSequences | x + h ∉ restrictedProductSpace} :=
    ((show Measurable (fun x : RealSequences => x + h) from by fun_prop)
      measurable_restrictedProductSpace).compl
  rw [restrictedProductStages.limit_apply _ hbad]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  exact ae_shift_mem_stageMeasure h hh n

theorem map_shift_restrictedProductMeasure_compl (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    (restrictedProductMeasure.map (fun x => x + h)) restrictedProductSpaceᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) measurable_restrictedProductSpace.compl]
  exact ae_shift_mem_restrictedProductMeasure h hh









end MeasureEquivalenceRestrictedProduct


