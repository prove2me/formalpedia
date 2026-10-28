-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedMass
-- name    : BenchmarkOperator20261026_RestrictedMass
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:47:46.309705+00:00
-- url     : https://prove2.me/theorems/5e40eb32-348b-4b4a-880b-16aab9dea184
-- title:
--   Restricted Mass
-- statement:
--   Defines tail-stay and eventual-stay events and their probabilities. The retained measurability, finite-product and limiting identities provide the mass calculations for these events under a real displacement.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedMass.lean, lines 11–123; source SHA-256 da1a46ebc1230a58ea6e07b2c87d15b35c4d64b3df326f2b7335835e13163f32. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_RestrictedSupport
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
import Mathlib.Probability.Independence.InfinitePi
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
open scoped ENNReal Topology NNReal

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def tailStaySet (h : RealSequences) (N : ℕ) : Set RealSequences :=
  {x | ∀ k, x k + h (N + k) ∈ baseInterval}

def tailStayProbability (h : RealSequences) (N : ℕ) : ℝ≥0∞ :=
  tailProbability (tailStaySet h N)

theorem measurable_tailStaySet (h : RealSequences) (N : ℕ) :
    MeasurableSet (tailStaySet h N) := by
  simpa only [tailStaySet, Set.setOf_forall] using MeasurableSet.iInter (fun k : ℕ =>
    ((measurable_pi_apply k).add_const (h (N + k)))
      (show MeasurableSet baseInterval from measurableSet_Icc))

theorem exponentialMeasure_add_preimage (a : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    exponentialMeasure ((fun t : ℝ => t + a) ⁻¹' s) =
      ENNReal.ofReal (Real.exp a) * exponentialMeasure s := by
  have he := congrArg (fun μ : Measure ℝ => μ s) (map_add_exponentialMeasure a)
  dsimp only at he
  rw [Measure.map_apply (by fun_prop) hs, Measure.smul_apply, smul_eq_mul] at he
  exact he

theorem fin_prod_ofReal_exp (n : ℕ) (h : RealSequences) :
    (∏ i : Fin n, ENNReal.ofReal (Real.exp (h i))) =
      ENNReal.ofReal (Real.exp (∑ i : Fin n, h i)) := by
  simp only [← coe_expNNReal, ← ENNReal.coe_finsetProd]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_prod, expNNReal, Real.exp_sum]
  rfl





def eventualStaySet (h : RealSequences) (N : ℕ) : Set RealSequences :=
  {x | ∀ k, N ≤ k → x k + h k ∈ baseInterval}

theorem measurable_eventualStaySet (h : RealSequences) (N : ℕ) :
    MeasurableSet (eventualStaySet h N) := by
  simpa only [eventualStaySet, Set.setOf_forall] using MeasurableSet.iInter (fun k : ℕ =>
    MeasurableSet.iInter (fun _ : N ≤ k =>
      ((measurable_pi_apply k).add_const (h k))
        (show MeasurableSet baseInterval from measurableSet_Icc)))

theorem tailStayProbability_eq_eventual (h : RealSequences) (N : ℕ) :
    tailStayProbability h N = tailProbability (eventualStaySet h N) := by
  have hm : tailProbability.map (fun x k => x (N + k)) = tailProbability :=
    Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => baseMeasure) (f := fun k => N + k)
      (fun _ _ hij => Nat.add_left_cancel hij)
  unfold tailStayProbability
  conv_lhs => rw [← hm]
  rw [Measure.map_apply (by fun_prop) (measurable_tailStaySet h N)]
  congr 1
  ext x
  constructor
  · intro hx k hk
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hx r
  · intro hx k
    exact hx (N + k) (Nat.le_add_right _ _)

theorem tendsto_tailStayProbability (h : RealSequences)
    (hh : Summable (fun n => |h n|)) :
    Tendsto (tailStayProbability h) atTop (𝓝 1) := by
  have hmono : Monotone (eventualStaySet h) := by
    intro n m hnm x hx k hmk
    exact hx k (hnm.trans hmk)
  have hae : ∀ᵐ x ∂tailProbability, x ∈ ⋃ N, eventualStaySet h N := by
    filter_upwards [ae_shift_mem_tailProbability h hh] with x hx
    obtain ⟨N, hN⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨N, hN⟩
  have hmass : tailProbability (⋃ N, eventualStaySet h N) = 1 :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (measurable_eventualStaySet h))).mp hae
  have ht := tendsto_measure_iUnion_atTop (μ := tailProbability) hmono
  rw [hmass] at ht
  have he : (tailProbability ∘ eventualStaySet h) = tailStayProbability h := by
    funext N
    exact (tailStayProbability_eq_eventual h N).symm
  rw [he] at ht
  exact ht



end MeasureEquivalenceRestrictedProduct


