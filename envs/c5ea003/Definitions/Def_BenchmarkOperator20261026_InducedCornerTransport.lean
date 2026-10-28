-- Prove2me | Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
-- name    : BenchmarkOperator20261026_InducedCornerTransport
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:30:10.450665+00:00
-- url     : https://prove2.me/theorems/baf582e4-0f42-4379-bdcf-2be1245396e6
-- title:
--   Induced Corner Transport
-- statement:
--   Defines the finite-corner measure on a base set times a counting-measure group coordinate, together with the orbit observable $(x,g)\mapsto g\cdot x$ and the coordinate translation maps. The retained measurability and measure-preservation facts justify these concrete transports.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization InducedCornerTransport.lean, lines 22–91; source SHA-256 62c274462557d556c2eb9fa9d7c218cee0ea0903508ec157c0f483c6a91d6df9. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
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

/-! Genuine finite-corner induced-module transports on the product of
the base sample space and the counting-measure group coordinate. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

noncomputable section

open MeasureEquivalenceEquidecomposition

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]

def indexRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

def indexLeft (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulLeft g
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

omit [Group G] [Countable G] in
theorem count_preserving (e : G ≃ᵐ G) :
    MeasurePreserving e (Measure.count : Measure G) Measure.count := by
  refine ⟨e.measurable, ?_⟩
  ext S hS
  rw [Measure.map_apply e.measurable hS]
  have he : e ⁻¹' S = e.symm '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, MeasurableEquiv.apply_symm_apply] using hy
  rw [he]
  exact Measure.count_injective_image e.symm.injective S

def diagonalEquiv (g : G) : (Z × G) ≃ᵐ (Z × G) :=
  (MeasurableEquiv.smul g).prodCongr (indexRight g⁻¹)

def indexShift (g : G) : (Z × G) ≃ᵐ (Z × G) :=
  (MeasurableEquiv.refl Z).prodCongr (indexLeft g)

def orbitPoint (p : Z × G) : Z := p.2 • p.1

theorem orbitPoint_measurable : Measurable (orbitPoint (G := G) (Z := Z)) :=
  measurable_from_prod_countable_left (fun g => measurable_const_smul g)





def cornerMeasure (μ : Measure Z) (A : Set Z) : Measure (Z × G) :=
  (μ.restrict A).prod Measure.count



variable (μ : Measure Z) [SigmaFinite μ]
    (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)



omit [MulAction G Z] [MeasurableConstSMul G Z] in
theorem indexShift_preserving (A : Set Z) (g : G) :
    MeasurePreserving (indexShift (Z := Z) g)
      (cornerMeasure (G := G) μ A) (cornerMeasure μ A) :=
  (MeasurePreserving.id (μ.restrict A)).prod (count_preserving (indexLeft g))



end
end MeasureEquivalenceInducedCorners


