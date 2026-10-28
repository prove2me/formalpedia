-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
-- name    : BenchmarkOperator20261026_MeasureUnitaryMultipliers
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:30:24.237208+00:00
-- url     : https://prove2.me/theorems/856543f3-6459-46d5-8f0f-20b95e8ea6fd
-- title:
--   Measure Unitary Multipliers
-- statement:
--   Defines multiplication by a measurable unit-modulus complex function as a linear isometry and as a genuine unitary of $L^2$. The representative and inverse formulas needed to construct these maps are retained. These are the phase multipliers used in the representation families.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureUnitaryMultipliers.lean, lines 17–77; source SHA-256 004e77cbbca2123bec893189d4ce85a753a03c359aacf2b9c5bd1bb40177c094. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

/-! Genuine multiplication unitaries in complex L², and their natural
intertwining by the square-root Radon–Nikodym unitary. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (c : α → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)

include hc hnorm

theorem phase_memLp (f : Lp E 2 μ) : MemLp (fun x => c x • f x) 2 μ := by
  apply (Lp.memLp f).congr_norm (hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f))
  exact .of_forall (fun x => by
    change ‖f x‖ = ‖c x • f x‖
    rw [norm_smul, hnorm x, one_mul])

noncomputable def phaseMap (f : Lp E 2 μ) : Lp E 2 μ :=
  (phase_memLp μ c hc hnorm f).toLp (fun x => c x • f x)

theorem phaseMap_coe (f : Lp E 2 μ) : phaseMap μ c hc hnorm f =ᵐ[μ] fun x => c x • f x :=
  (phase_memLp μ c hc hnorm f).coeFn_toLp

noncomputable def phaseLI : Lp E 2 μ →ₗᵢ[ℂ] Lp E 2 μ where
  toFun := phaseMap μ c hc hnorm
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [phaseMap_coe μ c hc hnorm (f + g), phaseMap_coe μ c hc hnorm f,
      phaseMap_coe μ c hc hnorm g,
      Lp.coeFn_add (phaseMap μ c hc hnorm f) (phaseMap μ c hc hnorm g), Lp.coeFn_add f g]
      with x hfg hf hg hadd hsource
    simp only [Pi.add_apply] at hadd hsource
    rw [hfg, hadd, hf, hg, hsource, smul_add]
  map_smul' := by
    intro a f
    apply Lp.ext
    filter_upwards [phaseMap_coe μ c hc hnorm (a • f), phaseMap_coe μ c hc hnorm f,
      Lp.coeFn_smul a (phaseMap μ c hc hnorm f), Lp.coeFn_smul a f]
      with x haf hf hsmul hsource
    simp only [Pi.smul_apply] at hsmul hsource
    simp only [RingHom.id_apply]
    rw [haf, hsmul, hf, hsource]
    exact smul_comm _ _ _
  norm_map' := by
    intro f
    change ‖phaseMap μ c hc hnorm f‖ = ‖f‖
    rw [phaseMap, Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (.of_forall (fun x => by simp only [norm_smul, hnorm x, one_mul]))

omit hc in
theorem inversePhase_norm (x : α) : ‖(c x)⁻¹‖ = 1 := by rw [norm_inv, hnorm x, inv_one]

theorem phaseMap_inverse (f : Lp E 2 μ) :
    phaseMap μ c hc hnorm
      (phaseMap μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f) = f := by
  apply Lp.ext
  filter_upwards [phaseMap_coe μ c hc hnorm
    (phaseMap μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f),
    phaseMap_coe μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f] with x houter hinner
  have hne : c x ≠ 0 := by
    intro hz
    have := hnorm x
    simp [hz] at this
  rw [houter, hinner, smul_smul, mul_inv_cancel₀ hne, one_smul]

noncomputable def phaseEquiv : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (phaseLI μ c hc hnorm) (by
    intro f
    exact ⟨phaseMap μ (fun x => (c x)⁻¹) hc.inv (inversePhase_norm c hnorm) f,
      phaseMap_inverse μ c hc hnorm f⟩)

variable (ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]



end MeasureUnitary


