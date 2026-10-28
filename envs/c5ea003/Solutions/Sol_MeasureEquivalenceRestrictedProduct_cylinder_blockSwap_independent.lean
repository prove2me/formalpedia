-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.cylinder_blockSwap_independent
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:39:00.57367+00:00
-- url     : https://prove2.me/submissions/76e37584-ed71-4e76-abaf-83ae42755e19

import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPermutation
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

-- Preserved source skeleton: RestrictedPermutation
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct







theorem blockSwap_small (N k : ℕ) (hk : k < N) : blockSwap N k = N + k := by
  exact if_pos hk







theorem measurable_permute (e : Equiv.Perm ℕ) : Measurable (permute e) :=
  measurable_pi_lambda _ (fun k => measurable_pi_apply (e k))

theorem measurePreserving_permute (e : Equiv.Perm ℕ) :
    MeasurePreserving (permute e) tailProbability tailProbability := by
  constructor
  · exact measurable_permute e
  · exact Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => baseMeasure) e.injective

theorem disjoint_image_blockSwap (s : Finset ℕ) (N : ℕ) (hs : s ⊆ Finset.range N) :
    Disjoint s (s.image (blockSwap N)) := by
  apply Finset.disjoint_left.mpr
  intro k hk hki
  obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hki
  have hkN := Finset.mem_range.mp (hs hk)
  have hjN := Finset.mem_range.mp (hs hj)
  rw [blockSwap_small N j hjN] at hjk
  omega



end MeasureEquivalenceRestrictedProduct

end

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution (s : Finset ℕ) (N : ℕ) (hs : s ⊆ Finset.range N)
    (A : Set (s → ℝ)) (hA : MeasurableSet A) :
    tailProbability.real (cylinder s A ∩ (permute (blockSwap N)) ⁻¹' cylinder s A) =
      (tailProbability.real (cylinder s A)) ^ 2 := by
  let e := blockSwap N
  let T : Finset ℕ := s.image e
  let relabel : (T → ℝ) → (s → ℝ) := fun z i =>
    z ⟨e i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hr : Measurable relabel := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have hf : ProbabilityTheory.iIndepFun (fun i (x : RealSequences) => x i) tailProbability :=
    ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => baseMeasure)
      (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  have hd : Disjoint s T := disjoint_image_blockSwap s N hs
  have hi := ProbabilityTheory.iIndepFun.indepFun_finset s T hd hf
    (fun i => measurable_pi_apply i)
  have hi' : ProbabilityTheory.IndepFun (fun (x : RealSequences) (i : s) => x i)
      (fun (x : RealSequences) (i : s) => x (e i)) tailProbability := by
    simpa only [Function.comp_apply, id_eq, relabel] using hi.comp measurable_id hr
  have he := hi'.measure_inter_preimage_eq_mul A A hA hA
  have hBm : MeasurableSet (cylinder s A : Set RealSequences) := hA.cylinder s
  have hm : tailProbability ((permute e) ⁻¹' cylinder s A) = tailProbability (cylinder s A) := by
    rw [← Measure.map_apply (measurable_permute e) hBm, (measurePreserving_permute e).map_eq]
  change tailProbability (cylinder s A ∩ (permute e) ⁻¹' cylinder s A) =
    tailProbability (cylinder s A) * tailProbability ((permute e) ⁻¹' cylinder s A) at he
  rw [hm] at he
  change (tailProbability (cylinder s A ∩ (permute e) ⁻¹' cylinder s A)).toReal =
    (tailProbability (cylinder s A)).toReal ^ 2
  rw [he, ENNReal.toReal_mul, pow_two]
