-- Prove2me | solution 1 for MeasureEquivalenceErgodicDecomposition.exists_constant_average_limit_on_components
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:22:58.669537+00:00
-- url     : https://prove2.me/submissions/e8a3f86d-fdc7-42a8-b9e3-d26051e6882b

import Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
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
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_conditional_fiber_constant
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_measurable_invariant_representative
import Theorems.Thm_MeasureEquivalenceMarkov_completedCoupling_ae_equal_iff
import Theorems.Thm_MeasureEquivalenceMarkov_couplingTransition_ae_eq_integral_kernel
import Theorems.Thm_MeasureEquivalenceMarkov_couplingTransition_fixed_iff

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

-- Preserved source skeleton: CouplingMarkov
section
/-!
A stationary coupling gives an actual contraction of L2. The operator
is the adjoint of the first-coordinate pullback followed by the
second-coordinate pullback. Its fixed vectors are precisely the
functions with equal pullbacks on the coupling.
-/

open MeasureTheory Filter
open scoped InnerProduct

namespace MeasureEquivalenceMarkov

section Hilbert

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]



theorem isometryTransition_norm_le_one (i j : E →ₗᵢ[ℝ] F) :
    ‖isometryTransition i j‖ ≤ 1 := by
  have hi : ‖i.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  have hj : ‖j.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp
  calc
    _ ≤ ‖i.toContinuousLinearMap.adjoint‖ * ‖j.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (by simpa using hi) hj (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num



end Hilbert

section Coupling

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)







theorem couplingTransition_norm_le_one : ‖couplingTransition μ J hfst hsnd‖ ≤ 1 :=
  isometryTransition_norm_le_one _ _



end Coupling

end MeasureEquivalenceMarkov

end

-- Preserved source skeleton: MetropolisCoupling
section
/-! Explicit stationary couplings from overlap measures along a
measurable automorphism. Their edges detect invariance. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]









theorem acceptanceFlow_equivalent (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z)
    (h : μ ≪ μ.map e) : μ ≪ acceptanceFlow μ e ∧ acceptanceFlow μ e ≪ μ := by
  constructor
  · apply withDensity_absolutelyContinuous'
    · exact (measurable_const.min (Measure.measurable_rnDeriv _ _)).aemeasurable
    · filter_upwards [Measure.rnDeriv_pos' h] with z hz
      exact (lt_min zero_lt_one hz).ne'
  · exact withDensity_absolutelyContinuous _ _





















end MeasureEquivalenceMarkov

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























theorem normalizedMetropolisTransition_norm_le_one (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ) :
    ‖normalizedMetropolisTransition μ e hmap‖ ≤ 1 := couplingTransition_norm_le_one _ _ _ _

theorem normalizedMetropolisTransition_fixed_iff (μ : Measure Z) [IsFiniteMeasure μ]
    (e : ℕ → Z ≃ᵐ Z) (hmap : ∀ n, μ.map (e n) ≪ μ)
    (hback : ∀ n, μ ≪ μ.map (e n)) (f : Lp ℝ 2 μ) :
    normalizedMetropolisTransition μ e hmap f = f ↔
      ∀ n, ∀ᵐ z ∂μ, f z = f ((e n).symm z) := by
  unfold normalizedMetropolisTransition
  rw [couplingTransition_fixed_iff, normalizedMetropolisCoupling,
    Measure.ae_ennreal_smul_measure_iff (by simp), metropolisMixtureCoupling,
    couplingMixture_ae_iff _ _ geometricWeights_ne_zero]
  exact forall_congr' (fun n => completedCoupling_ae_equal_iff μ (acceptanceFlow μ (e n)) (e n)
    (acceptanceFlow_equivalent μ (e n) (hback n)).2
    (acceptanceFlow_equivalent μ (e n) (hback n)).1 f (Lp.stronglyMeasurable f).measurable)

end MeasureEquivalenceMarkov

end

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

-- Preserved source skeleton: OrbitMarkov
section
/-! The actual Markov kernel of the Metropolis coupling stays in the
countable move relation and preserves the original measure. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]











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

theorem couplingTransition_ae_eq_condKernel (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f =ᵐ[μ] fun z => ∫ y, f y ∂J.condKernel z :=
  couplingTransition_ae_eq_integral_kernel μ J hfst hsnd J.condKernel
    (coupling_condKernel_joint μ J hfst).symm f



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

theorem normalizedMetropolisTransition_ae_eq_kernel (f : Lp ℝ 2 μ) :
    normalizedMetropolisTransition μ e hmap f =ᵐ[μ]
      fun z => ∫ y, f y ∂metropolisKernel μ e hmap z := by
  letI := normalizedMetropolisCoupling_finite μ e hmap
  exact couplingTransition_ae_eq_condKernel μ _
    (normalizedMetropolisCoupling_marginals μ e hmap).1
    (normalizedMetropolisCoupling_marginals μ e hmap).2 f







end ConcreteKernel

end MeasureEquivalenceMarkov

end

-- Preserved source skeleton: KernelAverages
section
/-! Actual bounded kernel iterates, Cesaro averages, and almost-everywhere
subsequences of their Hilbert mean-ergodic limits. -/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal Topology

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]



















theorem kernelApply_congr_ae (μ : Measure Z) (P : Kernel Z Z)
    (hstationary : P ∘ₘ μ = μ) {f g : Z → ℝ} (hfg : f =ᵐ[μ] g) :
    kernelApply P f =ᵐ[μ] kernelApply P g := by
  have h := Measure.ae_ae_of_ae_comp (by rwa [hstationary] : f =ᵐ[P ∘ₘ μ] g)
  exact h.mono (fun z hz => integral_congr_ae hz)









private theorem lp_finset_sum_coe (μ : Measure Z) {ι : Type*}
    (s : Finset ι) (u : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, u i : Lp ℝ 2 μ) =ᵐ[μ] fun z => ∑ i ∈ s, u i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (μ := μ) (E := ℝ) (p := 2))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with z hz hsum
    simpa only [Pi.add_apply, Finset.sum_insert ha] using hz.trans (congrArg (fun v => u a z + v) hsum)

section L2

variable (μ : Measure Z) (P : Kernel Z Z)
    (hstationary : P ∘ₘ μ = μ)
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hL : ∀ f : Lp ℝ 2 μ, L f =ᵐ[μ] kernelApply P f)

include hstationary hL

theorem iterate_ae_eq_kernelIterate (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∀ n, (L^[n] (hf.toLp f)) =ᵐ[μ] kernelIterate P f n := by
  intro n
  induction n with
  | zero => exact hf.coeFn_toLp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hL _).trans (kernelApply_congr_ae μ P hstationary ih)

theorem birkhoffAverage_ae_eq_kernelAverage (f : Z → ℝ) (hf : MemLp f 2 μ) (n : ℕ) :
    (birkhoffAverage ℝ L id n (hf.toLp f) : Lp ℝ 2 μ) =ᵐ[μ] kernelAverage P f n := by
  have hall := ae_all_iff.mpr (iterate_ae_eq_kernelIterate μ P hstationary L hL f hf)
  unfold birkhoffAverage birkhoffSum
  simp only [id_eq]
  filter_upwards [hall,
    Lp.coeFn_smul (n : ℝ)⁻¹ (∑ k ∈ range n, L^[k] (hf.toLp f)),
    lp_finset_sum_coe μ (range n) (fun k => L^[k] (hf.toLp f))] with z hz hsm hsum
  rw [hsm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  unfold kernelAverage
  congr 1
  exact sum_congr rfl (fun k _ => hz k)

/-- A genuine almost-everywhere subsequence of the Hilbert mean-ergodic
limit, written in terms of the actual pointwise kernel averages. -/
theorem exists_kernelAverage_subseq_tendsto_ae
    (hLnorm : ‖L‖ ≤ 1) (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂μ, Tendsto (fun n => kernelAverage P f (ns n) z) atTop
        (𝓝 (((LinearMap.eqLocus L 1).orthogonalProjection (hf.toLp f) : Lp ℝ 2 μ) z)) := by
  have ht := L.tendsto_birkhoffAverage_orthogonalProjection hLnorm (hf.toLp f)
  obtain ⟨ns, hns, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr (birkhoffAverage_ae_eq_kernelAverage μ P hstationary L hL f hf)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hAE, hall] with z hz heq
  exact hz.congr' (Eventually.of_forall (fun n => heq (ns n)))

end L2

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



theorem groupEnumeration_surjective : Function.Surjective (groupEnumeration G) :=
  (exists_surjective_nat G).choose_spec



theorem ac_of_inverse_map_ac (μ : Measure Z) (e : Z ≃ᵐ Z) (h : μ.map e.symm ≪ μ) :
    μ ≪ μ.map e := by
  have h' := h.map e.measurable
  have heq : (μ.map e.symm).map e = μ := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply]
    exact Measure.map_id
  rw [heq] at h'
  exact h'

variable (μ : Measure Z)
    (hns : ∀ g : G, Measure.QuasiMeasurePreserving (fun z : Z => g • z) μ μ)

include hns



theorem groupMoves_back_ac : ∀ n, μ ≪ μ.map (groupMoves (G := G) (Z := Z) n) := by
  intro n
  apply ac_of_inverse_map_ac
  simpa only [groupMoves, MeasurableEquiv.symm_symm, MeasurableEquiv.smul_apply] using
    (hns (groupEnumeration G n)).absolutelyContinuous

theorem groupTransition_fixed_iff [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    normalizedMetropolisTransition μ (groupMoves (G := G)) (groupMoves_ac μ hns) f = f ↔
      ∀ g : G, (fun z => f (g • z)) =ᵐ[μ] f := by
  rw [normalizedMetropolisTransition_fixed_iff μ _ (groupMoves_ac μ hns) (groupMoves_back_ac μ hns)]
  constructor
  · intro h g
    obtain ⟨n, hn⟩ := groupEnumeration_surjective (G := G) g
    filter_upwards [h n] with z hz
    simpa only [groupMoves, MeasurableEquiv.symm_symm, MeasurableEquiv.smul_apply, hn] using hz.symm
  · intro h n
    filter_upwards [h (groupEnumeration G n)] with z hz
    simpa only [groupMoves, MeasurableEquiv.symm_symm, MeasurableEquiv.smul_apply] using hz.symm



end MeasureEquivalenceMarkov

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

omit [MeasurableEq Z]

theorem solution (f : Z → ℝ) (hf : MemLp f 2 μ) :
    ∀ᵐ x ∂μ, ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ c : ℝ,
      ∀ᵐ z ∂invariantConditionalKernel (G := G) μ x,
        Tendsto (fun n => kernelAverage
          (metropolisKernel μ (groupMoves (G := G)) (groupMoves_ac μ hns)) f (ns n) z)
          atTop (𝓝 c) := by
  let e : ℕ → Z ≃ᵐ Z := groupMoves (G := G)
  let hm : ∀ n, μ.map (e n) ≪ μ := groupMoves_ac μ hns
  let P := metropolisKernel μ e hm
  let L := normalizedMetropolisTransition μ e hm
  let v : Lp ℝ 2 μ := (LinearMap.eqLocus L 1).orthogonalProjection (hf.toLp f)
  have hL : ∀ u : Lp ℝ 2 μ, L u =ᵐ[μ] kernelApply P u :=
    fun u => normalizedMetropolisTransition_ae_eq_kernel μ e hm u
  obtain ⟨ns, hmono, hlim⟩ := exists_kernelAverage_subseq_tendsto_ae μ P
    (metropolisKernel_stationary μ e hm) L hL
    (normalizedMetropolisTransition_norm_le_one μ e hm) f hf
  have hvfix : L v = v := ((LinearMap.eqLocus L 1).orthogonalProjection (hf.toLp f)).property
  have hvinv : ∀ g : G, (fun z => v (g • z)) =ᵐ[μ] v :=
    (groupTransition_fixed_iff μ hns v).mp hvfix
  obtain ⟨v', hv'm, hv'eq⟩ := measurable_invariant_representative μ v
    (Lp.stronglyMeasurable v).measurable (fun g => measurable_const_smul g) hvinv
  have hlim' : ∀ᵐ z ∂μ,
      Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 (v' z)) := by
    filter_upwards [hlim, hv'eq] with z hz heq
    rwa [heq]
  have hcomp := Measure.ae_ae_of_ae_comp
    (by rwa [invariantConditionalKernel_comp] :
      ∀ᵐ z ∂invariantConditionalKernel (G := G) μ ∘ₘ μ,
        Tendsto (fun n => kernelAverage P f (ns n) z) atTop (𝓝 (v' z)))
  have hc := conditional_fiber_constant μ (v' : InvariantBase G Z → ℝ) hv'm
  filter_upwards [hcomp, hc] with x hx hcx
  refine ⟨ns, hmono, v' x, ?_⟩
  filter_upwards [hx, hcx] with z hz hcz
  change v' z = v' x at hcz
  rwa [hcz] at hz
