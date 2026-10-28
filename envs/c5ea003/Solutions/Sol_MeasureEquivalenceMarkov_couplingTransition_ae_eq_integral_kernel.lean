-- Prove2me | solution 1 for MeasureEquivalenceMarkov.couplingTransition_ae_eq_integral_kernel
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:21:34.115138+00:00
-- url     : https://prove2.me/submissions/510e51bd-b720-440d-97b5-60ad8fcd69e7

import Definitions.Def_BenchmarkOperator20261026_CouplingMarkov
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
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

-- Preserved source skeleton: CouplingKernel
section
/-! The L2 coupling transition is the actual pointwise kernel integral. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal InnerProduct

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

theorem couplingTransition_setIntegral (f : Lp ℝ 2 μ) (s : Set Z) (hs : MeasurableSet s) :
    (∫ z in s, couplingTransition μ J hfst hsnd f z ∂μ) =
      ∫ z in Prod.fst ⁻¹' s, f z.2 ∂J := by
  let hpf : MeasurePreserving Prod.fst J μ := ⟨measurable_fst, hfst⟩
  let hps : MeasurePreserving Prod.snd J μ := ⟨measurable_snd, hsnd⟩
  let I : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℝ)
  calc
    _ = inner ℝ I (couplingTransition μ J hfst hsnd f) :=
      (L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) _).symm
    _ = inner ℝ (couplingFirst μ J hfst I) (couplingSecond μ J hsnd f) := by
      change inner ℝ I ((couplingFirst μ J hfst).toContinuousLinearMap.adjoint
        ((couplingSecond μ J hsnd).toContinuousLinearMap f)) = _
      exact ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ∫ z in Prod.fst ⁻¹' s, couplingSecond μ J hsnd f z ∂J := by
      change inner ℝ (Lp.compMeasurePreserving Prod.fst hpf I) _ = _
      rw [Lp.indicatorConstLp_compMeasurePreserving hs (measure_ne_top μ s) (1 : ℝ) hpf]
      exact L2.inner_indicatorConstLp_one (hs.preimage measurable_fst) _ _
    _ = _ := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving f hps)



end MeasureEquivalenceMarkov

end

/-! The L2 coupling transition is the actual pointwise kernel integral. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal InnerProduct
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
open MeasureEquivalenceMarkov
variable {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (J : Measure (Z × Z))
    (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

theorem solution
    (κ : Kernel Z Z) [IsFiniteKernel κ] (hJ : J = μ ⊗ₘ κ)
    (f : Lp ℝ 2 μ) :
    couplingTransition μ J hfst hsnd f =ᵐ[μ] fun z => ∫ y, f y ∂κ z := by
  have hfμ : Integrable f μ := MemLp.integrable (by norm_num) (Lp.memLp f)
  have hPfμ : Integrable (couplingTransition μ J hfst hsnd f) μ :=
    MemLp.integrable (by norm_num) (Lp.memLp _)
  have hfJ : Integrable (fun z : Z × Z => f z.2) J :=
    (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩).integrable_comp_of_integrable hfμ
  have hstationary : κ ∘ₘ μ = μ := by
    rw [← Measure.snd_compProd, ← hJ]
    exact hsnd
  have hfcomp : Integrable f (κ ∘ₘ μ) := by rwa [hstationary]
  have hnormI := Measure.integrable_integral_norm_of_integrable_comp hfcomp
  have hkernelI : Integrable (fun z => ∫ y, f y ∂κ z) μ := by
    apply Integrable.mono' hnormI (Lp.stronglyMeasurable f).integral_kernel.aestronglyMeasurable
    exact Eventually.of_forall (fun z => norm_integral_le_integral_norm _)
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hPfμ hkernelI
  intro s hs _
  rw [couplingTransition_setIntegral μ J hfst hsnd f s hs]
  have hset : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set Z) := by ext z; simp
  rw [hset, hJ]
  rw [Measure.setIntegral_compProd hs MeasurableSet.univ (by simpa [← hJ] using hfJ.integrableOn)]
  simp
