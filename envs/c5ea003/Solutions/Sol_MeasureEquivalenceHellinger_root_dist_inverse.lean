-- Prove2me | solution 1 for MeasureEquivalenceHellinger.root_dist_inverse
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:16:13.323986+00:00
-- url     : https://prove2.me/submissions/97fbe75b-bba3-45f7-8d5c-0065c5e4607d

import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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

-- Preserved source skeleton: HellingerTransport
section
open MeasureTheory Filter

namespace MeasureEquivalenceHellinger

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]





theorem energy_map (e : α ≃ᵐ β) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] :
    energy (μ.map e) (ν.map e) (ρ.map e) = energy μ ν ρ := by
  unfold energy
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map μ ρ,
    e.measurableEmbedding.rnDeriv_map ν ρ] with x hμ hν
  rw [hμ, hν]

theorem energy_change_reference (μ ν ρ σ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    energy μ ν σ = energy μ ν ρ := by
  unfold energy
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with x hmx hnx
  simp only [Pi.mul_apply] at hmx hnx
  rw [← hmx, ← hnx, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul (ENNReal.toReal_nonneg),
    Real.sqrt_mul (ENNReal.toReal_nonneg)]
  nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (ρ.rnDeriv σ x).toReal)]

theorem energy_fixed_reference_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    energy (μ.map e) (ν.map e) ρ = energy μ ν ρ := by
  let : SigmaFinite (μ.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ν.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ρ.map e) := e.measurableEmbedding.sigmaFinite_map
  rw [energy_change_reference (μ.map e) (ν.map e) (ρ.map e) ρ
    (e.measurableEmbedding.absolutelyContinuous_map hμ)
    (e.measurableEmbedding.absolutelyContinuous_map hν) hρ]
  exact energy_map e μ ν ρ









theorem root_dist_sq (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dist (root μ ρ) (root ν ρ) ^ 2 = energy μ ν ρ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  unfold energy
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (root μ ρ) (root ν ρ), root_coe μ ρ,
    root_coe ν ρ] with x hs hμ hν
  simp only [Pi.sub_apply] at hs
  rw [hs, hμ, hν]
  simp [sq]

theorem root_dist_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    dist (root (μ.map e) ρ) (root (ν.map e) ρ) = dist (root μ ρ) (root ν ρ) := by
  have he := energy_fixed_reference_map e μ ν ρ hμ hν hρ
  rw [← root_dist_sq, ← root_dist_sq] at he
  nlinarith [dist_nonneg (x := root (μ.map e) ρ) (y := root (ν.map e) ρ),
    dist_nonneg (x := root μ ρ) (y := root ν ρ)]









end MeasureEquivalenceHellinger

end

open MeasureTheory Filter
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
open MeasureEquivalenceHellinger
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem solution (e f : α ≃ᵐ α) (ρ : Measure α) [IsFiniteMeasure ρ]
    (hcomm : Function.Commute e f)
    (he : ρ.map e ≪ ρ) (hf : ρ.map f ≪ ρ)
    (hei : ρ.map e.symm ≪ ρ) (hfi : ρ.map f.symm ≪ ρ) :
    dist (root (ρ.map e.symm) ρ) (root (ρ.map f.symm) ρ) =
      dist (root (ρ.map e) ρ) (root (ρ.map f) ρ) := by
  have ht : ρ.map (e.trans f) ≪ ρ := by
    have ht' := (f.measurableEmbedding.absolutelyContinuous_map he).trans hf
    simpa only [Measure.map_map f.measurable e.measurable,
      MeasurableEquiv.coe_trans] using ht'
  have hmap1 : (ρ.map e.symm).map (e.trans f) = ρ.map f := by
    rw [Measure.map_map (e.trans f).measurable e.symm.measurable]
    congr 1
    funext x
    simp
  have hmap2 : (ρ.map f.symm).map (e.trans f) = ρ.map e := by
    rw [Measure.map_map (e.trans f).measurable f.symm.measurable]
    congr 1
    funext x
    change f (e (f.symm x)) = e x
    rw [← hcomm (f.symm x), f.apply_symm_apply]
  have hd := root_dist_map (e.trans f) (ρ.map e.symm) (ρ.map f.symm) ρ hei hfi ht
  simp only [hmap1, hmap2] at hd
  exact hd.symm.trans (dist_comm _ _)
