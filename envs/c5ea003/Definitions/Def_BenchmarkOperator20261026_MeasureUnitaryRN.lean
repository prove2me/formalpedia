-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryRN
-- name    : BenchmarkOperator20261026_MeasureUnitaryRN
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:43:40.862734+00:00
-- url     : https://prove2.me/theorems/8efacc1c-7879-44e4-b9e6-a3c9be78baf3
-- title:
--   Measure Unitary RN
-- statement:
--   Defines the square-root Radon–Nikodym weight and its weighted linear isometry and unitary between $L^2$ spaces of equivalent sigma-finite measures. The retained representative, inner-product and inverse-weight identities justify this equivalence.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureUnitaryRN.lean, lines 18–105; source SHA-256 7d99590863297b3f2547fbd1b18a6b4f71402e83b42778b5e8a834f02ffec1c9. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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

/-! The genuine complex L² unitary associated to equivalent finite measures.
It multiplies by the square root of the Radon–Nikodym derivative. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def rnWeight (x : α) : ℝ := Real.sqrt (μ.rnDeriv ν x).toReal

theorem rnWeight_measurable : Measurable (rnWeight μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal.sqrt

theorem rnWeight_sq (x : α) : rnWeight μ ν x ^ 2 = (μ.rnDeriv ν x).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem rnWeight_norm_sq (f : α → E) (x : α) :
    ‖rnWeight μ ν x • f x‖ ^ 2 = (μ.rnDeriv ν x).toReal * ‖f x‖ ^ 2 := by
  have hw : 0 ≤ rnWeight μ ν x := Real.sqrt_nonneg _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, mul_pow, rnWeight_sq]

theorem rnWeighted_memLp (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) :
    MemLp (fun x => rnWeight μ ν x • f x) 2 ν := by
  have hf : AEStronglyMeasurable (fun x => f x) ν :=
    AEStronglyMeasurable.mono_ac hνμ (Lp.aestronglyMeasurable f)
  apply (memLp_two_iff_integrable_sq_norm ((rnWeight_measurable μ ν).aestronglyMeasurable.smul hf)).mpr
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  simpa only [rnWeight_norm_sq] using
    (integrable_toReal_rnDeriv_mul_iff hμν).mpr hi

noncomputable def rnWeightedMap (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) : Lp E 2 ν :=
  (rnWeighted_memLp μ ν hμν hνμ f).toLp (fun x => rnWeight μ ν x • f x)

theorem rnWeightedMap_coe (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) :
    rnWeightedMap μ ν hμν hνμ f =ᵐ[ν] fun x => rnWeight μ ν x • f x :=
  (rnWeighted_memLp μ ν hμν hνμ f).coeFn_toLp

theorem rnWeightedMap_inner (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f g : Lp E 2 μ) :
    inner ℂ (rnWeightedMap μ ν hμν hνμ f) (rnWeightedMap μ ν hμν hνμ g) = inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def, ← integral_rnDeriv_smul hμν]
  apply integral_congr_ae
  filter_upwards [rnWeightedMap_coe μ ν hμν hνμ f, rnWeightedMap_coe μ ν hμν hνμ g] with x hf hg
  rw [hf, hg, inner_smul_left_eq_smul, inner_smul_right_eq_smul, smul_smul,
    ← pow_two, rnWeight_sq]

noncomputable def rnWeightedLI (hμν : μ ≪ ν) (hνμ : ν ≪ μ) : Lp E 2 μ →ₗᵢ[ℂ] Lp E 2 ν where
  toFun := rnWeightedMap μ ν hμν hνμ
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [rnWeightedMap_coe μ ν hμν hνμ (f + g),
      rnWeightedMap_coe μ ν hμν hνμ f, rnWeightedMap_coe μ ν hμν hνμ g,
      Lp.coeFn_add (rnWeightedMap μ ν hμν hνμ f) (rnWeightedMap μ ν hμν hνμ g),
      hνμ.ae_eq (Lp.coeFn_add f g)] with x hfg hf hg hadd hsource
    simp only [Pi.add_apply] at hadd hsource
    rw [hfg, hadd, hf, hg, hsource]
    exact smul_add _ _ _
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [rnWeightedMap_coe μ ν hμν hνμ (c • f), rnWeightedMap_coe μ ν hμν hνμ f,
      Lp.coeFn_smul c (rnWeightedMap μ ν hμν hνμ f), hνμ.ae_eq (Lp.coeFn_smul c f)]
      with x hcf hf hsmul hsource
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply] at hsmul hsource
    rw [hcf, hsmul, hf, hsource]
    exact smul_comm _ _ _
  norm_map' := by
    intro f
    change ‖rnWeightedMap μ ν hμν hνμ f‖ = ‖f‖
    have hi := rnWeightedMap_inner μ ν hμν hνμ f f
    have hr : ‖rnWeightedMap μ ν hμν hνμ f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hi]
    nlinarith [norm_nonneg (rnWeightedMap μ ν hμν hνμ f), norm_nonneg f]

theorem rnWeight_inverse_product (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (fun x => rnWeight ν μ x * rnWeight μ ν x) =ᵐ[μ] fun _ => 1 := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := μ) hμν, μ.rnDeriv_self] with x hx hself
  simp only [Pi.mul_apply] at hx
  rw [rnWeight, rnWeight, ← Real.sqrt_mul ENNReal.toReal_nonneg,
    ← ENNReal.toReal_mul, mul_comm (ν.rnDeriv μ x), hx, hself]
  norm_num

theorem rnWeightedMap_inverse (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) :
    rnWeightedMap ν μ hνμ hμν (rnWeightedMap μ ν hμν hνμ f) = f := by
  apply Lp.ext
  filter_upwards [rnWeightedMap_coe ν μ hνμ hμν (rnWeightedMap μ ν hμν hνμ f),
    hμν.ae_eq (rnWeightedMap_coe μ ν hμν hνμ f), rnWeight_inverse_product μ ν hμν hνμ]
    with x houter hinner hprod
  rw [houter, hinner, smul_smul, hprod, one_smul]

noncomputable def rnWeightedEquiv (hμν : μ ≪ ν) (hνμ : ν ≪ μ) : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν :=
  LinearIsometryEquiv.ofSurjective (rnWeightedLI μ ν hμν hνμ) (by
    intro g
    exact ⟨rnWeightedMap ν μ hνμ hμν g, rnWeightedMap_inverse ν μ hνμ hμν g⟩)

end MeasureUnitary


