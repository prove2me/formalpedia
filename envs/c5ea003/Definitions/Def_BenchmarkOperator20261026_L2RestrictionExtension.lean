-- Prove2me | Definitions.Def_BenchmarkOperator20261026_L2RestrictionExtension
-- name    : BenchmarkOperator20261026_L2RestrictionExtension
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:33:31.666992+00:00
-- url     : https://prove2.me/theorems/b4a4c9ac-4e9b-44e2-8ef4-fa16bcd854b9
-- title:
--   L2 Restriction Extension
-- statement:
--   Defines bounded restriction from the ambient complex $L^2$ space and isometric zero extension from a measurable restriction. The retained representative formulas and norm facts justify these linear maps. Their adjoint identities are separate supporting theorems.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization L2RestrictionExtension.lean, lines 17–84; source SHA-256 c1451e819e6f6bc6464b2002c2be402116d3e02f9916602adc4ac6307d532e2e. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
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

/-! Actual bounded restriction and isometric zero extension for complex
L2 spaces, including their projection and adjoint identities. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Restriction

open MeasureUnitary

noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def restrictMap (A : Set X) (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.restrict A) :=
  ((Lp.memLp f).restrict A).toLp f

theorem restrict_coe (A : Set X) (f : Lp ℂ 2 μ) :
    restrictMap μ A f =ᵐ[μ.restrict A] f := ((Lp.memLp f).restrict A).coeFn_toLp

theorem restrict_norm_le (A : Set X) (f : Lp ℂ 2 μ) :
    ‖restrictMap μ A f‖ ≤ ‖f‖ := by
  rw [restrictMap, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_restrict_le f 2 μ A)

def restrictCLM (A : Set X) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (μ.restrict A) :=
  LinearMap.mkContinuous
    { toFun := restrictMap μ A
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [restrict_coe μ A (f+g), restrict_coe μ A f, restrict_coe μ A g,
          Lp.coeFn_add (restrictMap μ A f) (restrictMap μ A g),
          ae_restrict_of_ae (Lp.coeFn_add f g)] with x hfg hf hg hadd hsource
        simp only [Pi.add_apply] at hadd hsource
        rw [hfg, hadd, hf, hg, hsource]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [restrict_coe μ A (c • f), restrict_coe μ A f,
          Lp.coeFn_smul c (restrictMap μ A f), ae_restrict_of_ae (Lp.coeFn_smul c f)]
          with x hcf hf hsmul hsource
        simp only [Pi.smul_apply] at hsmul hsource
        simp only [RingHom.id_apply]
        rw [hcf, hsmul, hf, hsource] }
    1 (fun f => by simpa only [one_mul] using restrict_norm_le μ A f)

def zeroExtend (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 (μ.restrict A)) : Lp ℂ 2 μ :=
  ((memLp_indicator_iff_restrict hA).mpr (Lp.memLp f)).toLp (A.indicator f)

theorem zeroExtend_coe (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 (μ.restrict A)) :
    zeroExtend μ A hA f =ᵐ[μ] A.indicator f :=
  ((memLp_indicator_iff_restrict hA).mpr (Lp.memLp f)).coeFn_toLp

theorem zeroExtend_norm (A : Set X) (hA : MeasurableSet A) (f : Lp ℂ 2 (μ.restrict A)) :
    ‖zeroExtend μ A hA f‖ = ‖f‖ := by
  rw [zeroExtend, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hA, Lp.norm_def]

def zeroExtendLI (A : Set X) (hA : MeasurableSet A) :
    Lp ℂ 2 (μ.restrict A) →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := zeroExtend μ A hA
  map_add' := by
    intro f g
    apply Lp.ext
    have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_add f g)
    filter_upwards [zeroExtend_coe μ A hA (f+g), zeroExtend_coe μ A hA f,
      zeroExtend_coe μ A hA g, Lp.coeFn_add (zeroExtend μ A hA f) (zeroExtend μ A hA g), hs]
      with x hfg hf hg hadd hsource
    simp only [Pi.add_apply] at hadd
    rw [hfg, hadd, hf, hg, hsource]
    by_cases hx : x ∈ A <;> simp [hx]
  map_smul' := by
    intro c f
    apply Lp.ext
    have hs := (ae_eq_restrict_iff_indicator_ae_eq hA).mp (Lp.coeFn_smul c f)
    filter_upwards [zeroExtend_coe μ A hA (c • f), zeroExtend_coe μ A hA f,
      Lp.coeFn_smul c (zeroExtend μ A hA f), hs] with x hcf hf hsmul hsource
    simp only [Pi.smul_apply] at hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul, hf, hsource]
    by_cases hx : x ∈ A <;> simp [hx]
  norm_map' := zeroExtend_norm μ A hA











end
end MeasureEquivalenceL2Restriction


