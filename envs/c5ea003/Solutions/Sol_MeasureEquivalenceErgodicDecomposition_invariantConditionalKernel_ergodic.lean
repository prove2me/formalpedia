-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.invariantConditionalKernel_ergodic
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:27:56.867363+00:00
-- url     : https://prove2.me/submissions/f321c2fa-6ff2-489c-8d41-d4984bef7db4

import Definitions.Def_BenchmarkOperator20261026_ConditionalFibers
import Definitions.Def_BenchmarkOperator20261026_CouplingMixture
import Definitions.Def_BenchmarkOperator20261026_GroupMarkov
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_KernelAverages
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Tactic
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_exists_constant_average_limit_on_components
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_stationary
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_setLIntegral_of_stationary_noLeak
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_zero_or_conull_of_test_factorization
import Theorems.Thm_MeasureEquivalenceMarkov_setIntegral_eq_mul_of_kernelAverage_limit

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

-- Preserved source skeleton: InvariantConditional
section
/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace MeasureEquivalenceErgodicDecomposition



variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]















section Conditional

variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]









/-- Integrating the invariant conditional kernel reconstructs the
original finite measure. -/
theorem invariantConditionalKernel_comp :
    invariantConditionalKernel (G := G) μ ∘ₘ μ = μ := by
  ext s hs
  have hcomp := congrArg (fun ρ : Measure Z => ρ s)
    (condExpKernel_comp_trim (μ := μ) (invariantSigma_le (G := G)))
  dsimp only at hcomp
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)] at hcomp ⊢
  change (∫⁻ z, condExpKernel μ (invariantSigma (G := G)) z s ∂μ) = μ s
  rw [← lintegral_trim (invariantSigma_le (G := G)) (measurable_condExpKernel hs)]
  exact hcomp

















end Conditional

end MeasureEquivalenceErgodicDecomposition

end

-- Preserved source skeleton: ConditionalFibers
section
/-! The actual invariant conditional kernel is constant almost everywhere
on almost every conditional fiber. Countability is used only for a family
that determines finite measures, so no AE/uncountable-forall swap is made. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceErgodicDecomposition

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]
    [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]





theorem determiningSet_measurable (s : Finset ℕ) : MeasurableSet (determiningSet (Z := Z) s) :=
  s.measurableSet_biInter (fun i _hi => MeasurableSpace.measurableSet_natGeneratingSequence (α := Z) i)











end MeasureEquivalenceErgodicDecomposition

end

-- Preserved source skeleton: CouplingMixture
section
/-! Countably many accepted couplings are combined into one contraction.
Positive weights retain precisely the intersection of all fixed spaces. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]







theorem couplingMixture_ae_iff (w : ℕ → ℝ≥0∞) (J : ℕ → Measure (Z × Z))
    (hw : ∀ n, w n ≠ 0) (P : Z × Z → Prop) :
    (∀ᵐ z ∂couplingMixture w J, P z) ↔ ∀ n, ∀ᵐ z ∂J n, P z := by
  rw [couplingMixture, Measure.ae_sum_iff]
  simp_rw [Measure.ae_ennreal_smul_measure_iff (hw _)]



theorem geometricWeights_ne_zero (n : ℕ) : geometricWeights n ≠ 0 := by
  unfold geometricWeights
  exact pow_ne_zero _ (by simp)



























end MeasureEquivalenceMarkov

end

-- Preserved source skeleton: OrbitMarkov
section
/-! The actual Markov kernel of the Metropolis coupling stays in the
countable move relation and preserves the original measure. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]



theorem moveRelation_measurable [MeasurableEq Z]
    (e : ℕ → Z ≃ᵐ Z) : MeasurableSet {z : Z × Z | moveRelation e z.1 z.2} := by
  have hset : {z : Z × Z | moveRelation e z.1 z.2} =
      {z : Z × Z | z.1 = z.2} ∪
        ⋃ n : ℕ, ({z : Z × Z | z.2 = e n z.1} ∪ {z : Z × Z | z.2 = (e n).symm z.1}) := by
    ext z
    simp [moveRelation]
  rw [hset]
  apply (measurableSet_eq_fun measurable_fst measurable_snd).union
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_eq_fun measurable_snd ((e n).measurable.comp measurable_fst)).union
    (measurableSet_eq_fun measurable_snd ((e n).symm.measurable.comp measurable_fst))

theorem completedCoupling_ae_relation (μ ν : Measure Z) (e : Z ≃ᵐ Z)
    (R : Z → Z → Prop) (hR : MeasurableSet {z : Z × Z | R z.1 z.2})
    (hdiag : ∀ z, R z z) (hedge : ∀ z, R z (e.symm z))
    (hreverse : ∀ z, R (e.symm z) z) :
    ∀ᵐ z ∂completedCoupling μ ν e, R z.1 z.2 := by
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) := measurable_id.prodMk e.symm.measurable
  have hdmap : Measurable (fun z : Z => (z,z)) := measurable_id.prodMk measurable_id
  have hA : ∀ᵐ z ∂acceptedEdges ν e, R z.1 z.2 :=
    (ae_map_iff hgraph.aemeasurable hR).mpr (Eventually.of_forall hedge)
  have hArev : ∀ᵐ z ∂acceptedEdges ν e, R z.2 z.1 :=
    (ae_map_iff hgraph.aemeasurable (hR.preimage measurable_swap)).mpr
      (Eventually.of_forall hreverse)
  have hAS : ∀ᵐ z ∂(acceptedEdges ν e).map Prod.swap, R z.1 z.2 :=
    (ae_map_iff measurable_swap.aemeasurable hR).mpr hArev
  have hD : ∀ᵐ z ∂((μ+μ) - (ν + ν.map e.symm)).map (fun z => (z,z)), R z.1 z.2 :=
    (ae_map_iff hdmap.aemeasurable hR).mpr (Eventually.of_forall hdiag)
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨hA,hAS⟩,hD⟩

theorem normalizedMetropolisCoupling_ae_moves [MeasurableEq Z]
    (μ : Measure Z) (e : ℕ → Z ≃ᵐ Z) :
    ∀ᵐ z ∂normalizedMetropolisCoupling μ e, moveRelation e z.1 z.2 := by
  apply Measure.ae_smul_measure
  apply (couplingMixture_ae_iff _ _ geometricWeights_ne_zero _).mpr
  intro n
  apply completedCoupling_ae_relation μ _ (e n) (moveRelation e) (moveRelation_measurable e)
  · intro z
    exact Or.inl rfl
  · intro z
    exact Or.inr ⟨n, Or.inr rfl⟩
  · intro z
    exact Or.inr ⟨n, Or.inl ((e n).apply_symm_apply z).symm⟩



section Kernel

variable [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z)) [IsFiniteMeasure J]
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

include hfst in
omit [IsFiniteMeasure μ] in
theorem coupling_condKernel_joint : μ ⊗ₘ J.condKernel = J := by
  simpa only [Measure.fst, hfst] using Measure.disintegrate J J.condKernel

include hfst hsnd in
theorem coupling_condKernel_stationary : J.condKernel ∘ₘ μ = μ := by
  rw [← Measure.snd_compProd, coupling_condKernel_joint μ J hfst]
  exact hsnd



include hfst in
theorem coupling_condKernel_ae_relation (R : Z → Z → Prop)
    (hR : ∀ᵐ z ∂J, R z.1 z.2) : ∀ᵐ z ∂μ, ∀ᵐ y ∂J.condKernel z, R z y := by
  apply Measure.ae_ae_of_ae_compProd (μ := μ) (κ := J.condKernel)
    (p := fun z : Z × Z => R z.1 z.2)
  rwa [coupling_condKernel_joint μ J hfst]

end Kernel

section ConcreteKernel

variable [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (e : ℕ → Z ≃ᵐ Z)
    (hmap : ∀ n, μ.map (e n) ≪ μ)







theorem metropolisKernel_stationary : metropolisKernel μ e hmap ∘ₘ μ = μ := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  exact coupling_condKernel_stationary μ _
    (normalizedMetropolisCoupling_marginals μ e hmap).1
    (normalizedMetropolisCoupling_marginals μ e hmap).2



theorem metropolisKernel_ae_moves [MeasurableEq Z] :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂metropolisKernel μ e hmap z, moveRelation e z y := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  exact coupling_condKernel_ae_relation μ _ (normalizedMetropolisCoupling_marginals μ e hmap).1
    (moveRelation e) (normalizedMetropolisCoupling_ae_moves μ e)

omit [StandardBorelSpace Z] [Nonempty Z] in
theorem moveRelation_mem_iff (s : Set Z)
    (hs : ∀ n, (e n) ⁻¹' s = s) {z y : Z} (hmove : moveRelation e z y) :
    y ∈ s ↔ z ∈ s := by
  have hmem (n : ℕ) (x : Z) : e n x ∈ s ↔ x ∈ s := by
    change x ∈ (e n) ⁻¹' s ↔ x ∈ s
    rw [hs n]
  rcases hmove with h | ⟨n,h | h⟩
  · rw [h]
  · rw [h]
    exact hmem n z
  · rw [h]
    simpa only [MeasurableEquiv.apply_symm_apply] using (hmem n ((e n).symm z)).symm

theorem metropolisKernel_ae_invariant_set [MeasurableEq Z] (s : Set Z)
    (hs : ∀ n, (e n) ⁻¹' s = s) :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂metropolisKernel μ e hmap z, y ∈ s ↔ z ∈ s := by
  filter_upwards [metropolisKernel_ae_moves μ e hmap] with z hz
  exact hz.mono (fun y hy => moveRelation_mem_iff e s hs hy)

end ConcreteKernel

end MeasureEquivalenceMarkov

end

-- Preserved source skeleton: GroupMarkov
section
/-! The concrete stationary transition for one countable nonsingular
group action, with fixed space exactly its invariant L2 functions. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z]









variable (μ : Measure Z)
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns







theorem groupKernel_noLeak [StandardBorelSpace Z] [Nonempty Z] [IsFiniteMeasure μ]
    [MeasurableEq Z] (s : Set Z)
    (hs : ∀ g : G, (fun z : Z => g • z) ⁻¹' s = s) :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂metropolisKernel μ (groupMoves (G := G)) (groupMoves_ac μ hns) z,
      y ∈ s ↔ z ∈ s := by
  apply metropolisKernel_ae_invariant_set
  intro n
  simpa only [groupMoves, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply] using
    hs (groupEnumeration G n)⁻¹

end MeasureEquivalenceMarkov

end

-- Preserved source skeleton: ErgodicComponents
section
/-! Actual ergodicity of almost every invariant conditional probability,
using one global Markov contraction and a mean-ergodic subsequence. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace MeasureEquivalenceErgodicDecomposition

open MeasureEquivalenceMarkov

variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableEq Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

omit [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z] in
theorem restricted_stationary_of_noLeak
    (ν : Measure Z) [IsFiniteMeasure ν] (P : Kernel Z Z) [IsMarkovKernel P]
    (hstat : P ∘ₘ ν = ν) (B : Set Z) (hB : MeasurableSet B)
    (hleak : ∀ᵐ z ∂ν, ∀ᵐ y ∂P z, y ∈ B ↔ z ∈ B) :
    P ∘ₘ ν.restrict B = ν.restrict B := by
  ext A hA
  rw [Measure.bind_apply hA P.aemeasurable, Measure.restrict_apply hA]
  exact (setLIntegral_of_stationary_noLeak ν P hstat B A hB hA hleak).trans
    (congrArg ν (inter_comm B A))





end MeasureEquivalenceErgodicDecomposition

end

/-! Actual ergodicity of almost every invariant conditional probability,
using one global Markov contraction and a mean-ergodic subsequence. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceErgodicDecomposition
open MeasureEquivalenceMarkov
variable {G Z : Type*} [Group G] [Countable G] [MeasurableSpace Z]
    [MulAction G Z] [MeasurableConstSMul G Z] [StandardBorelSpace Z] [Nonempty Z]
    [MeasurableEq Z]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns

theorem solution :
    ∀ᵐ x ∂μ, ∀ B : Set Z, MeasurableSet B →
      (∀ g : G, (fun z : Z => g • z) ⁻¹' B = B) →
      invariantConditionalKernel (G := G) μ x B = 0 ∨
        invariantConditionalKernel (G := G) μ x Bᶜ = 0 := by
  classical
  let e : ℕ → Z ≃ᵐ Z := groupMoves (G := G)
  let hm : ∀ n, μ.map (e n) ≪ μ := groupMoves_ac μ hns
  let P := metropolisKernel μ e hm
  let κ := invariantConditionalKernel (G := G) μ
  have hstat : P ∘ₘ μ = μ := metropolisKernel_stationary μ e hm
  have hκstat : ∀ᵐ x ∂μ, P ∘ₘ κ x = κ x := by
    apply invariantConditionalKernel_stationary μ P hstat
    intro B _hB hB
    exact groupKernel_noLeak μ hns B hB
  have hMoves : ∀ᵐ z ∂μ, ∀ᵐ y ∂P z, moveRelation e z y :=
    metropolisKernel_ae_moves μ e hm
  have hκMoves : ∀ᵐ x ∂μ, ∀ᵐ z ∂κ x, ∀ᵐ y ∂P z, moveRelation e z y := by
    apply Measure.ae_ae_of_ae_comp
    rwa [invariantConditionalKernel_comp]
  let test : Finset ℕ → Z → ℝ := fun s => (determiningSet s).indicator (fun _ => (1 : ℝ))
  have htestm (s : Finset ℕ) : Measurable (test s) :=
    measurable_const.indicator (determiningSet_measurable s)
  have htestb (s : Finset ℕ) : ∀ z, |test s z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ determiningSet (Z := Z) s
    · simp [test, Set.indicator_of_mem hz]
    · simp [test, Set.indicator_of_notMem hz]
  have htestLp (s : Finset ℕ) : MemLp (test s) 2 μ :=
    (memLp_const (1 : ℝ)).indicator (determiningSet_measurable s)
  have htests : ∀ s : Finset ℕ, ∀ᵐ x ∂μ,
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ c : ℝ,
        ∀ᵐ z ∂κ x, Tendsto (fun n => kernelAverage P (test s) (ns n) z) atTop (𝓝 c) := by
    intro s
    exact exists_constant_average_limit_on_components μ hns (test s) (htestLp s)
  have htestsAll := ae_all_iff.mpr htests
  filter_upwards [hκstat, hκMoves, htestsAll] with x hxstat hxMoves hxTests
  intro B hB hBinv
  let ν := κ x
  have hBmoves : ∀ n, (e n) ⁻¹' B = B := by
    intro n
    simpa only [e, groupMoves, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply] using
      hBinv (groupEnumeration G n)⁻¹
  have hnoLeak : ∀ᵐ z ∂ν, ∀ᵐ y ∂P z, y ∈ B ↔ z ∈ B := by
    filter_upwards [hxMoves] with z hz
    exact hz.mono (fun y hy => moveRelation_mem_iff e B hBmoves hy)
  have hBstat : P ∘ₘ ν.restrict B = ν.restrict B :=
    restricted_stationary_of_noLeak ν P hxstat B hB hnoLeak
  apply zero_or_conull_of_test_factorization ν B hB
  intro s
  obtain ⟨ns, hnsmono, c, hclim⟩ := hxTests s
  have hBint := setIntegral_eq_mul_of_kernelAverage_limit ν P B hBstat
    (test s) (htestm s) 1 zero_le_one (htestb s) ns hnsmono c hclim
  have hUint := setIntegral_eq_mul_of_kernelAverage_limit ν P Set.univ
    (by simpa only [Measure.restrict_univ] using hxstat)
    (test s) (htestm s) 1 zero_le_one (htestb s) ns hnsmono c hclim
  have hc : ν.real (determiningSet (Z := Z) s) = c := by
    simpa only [test, Measure.restrict_univ,
      integral_indicator_const (1 : ℝ) (determiningSet_measurable s),
      smul_eq_mul, mul_one, probReal_univ] using hUint
  have hleft : (∫ z in B, test s z ∂ν) = ν.real (determiningSet (Z := Z) s ∩ B) := by
    change (∫ z, (determiningSet (Z := Z) s).indicator (fun _ => (1 : ℝ)) z ∂ν.restrict B) = _
    rw [integral_indicator_const (1 : ℝ) (determiningSet_measurable s),
      measureReal_restrict_apply (determiningSet_measurable s), smul_eq_mul, mul_one]
  rw [hleft, ← hc] at hBint
  exact hBint
