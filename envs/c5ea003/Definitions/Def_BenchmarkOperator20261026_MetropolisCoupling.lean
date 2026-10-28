-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
-- name    : BenchmarkOperator20261026_MetropolisCoupling
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:27:17.16207+00:00
-- url     : https://prove2.me/theorems/dff61d74-b974-461e-a1df-bfb0b8dfe2cc
-- title:
--   Metropolis Coupling
-- statement:
--   Defines the accepted-flow measure, its graph-edge measure along a measurable automorphism, and the symmetrized coupling with a diagonal remainder. The retained bounds and marginal identities justify the coupling construction. Its detection of invariant functions is a later theorem.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MetropolisCoupling.lean, lines 15–103; source SHA-256 5dd4c9054ac0ec7fd9b84a78437c0872889d3343d7cfeb4991d7d2011bc25e51. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
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

/-! Explicit stationary couplings from overlap measures along a
measurable automorphism. Their edges detect invariance. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceMarkov

variable {Z : Type*} [MeasurableSpace Z]

/-- The bounded acceptance flow is the overlap of μ and its translate. -/
noncomputable def acceptanceFlow (μ : Measure Z) (e : Z ≃ᵐ Z) : Measure Z :=
  μ.withDensity (fun z => min 1 ((μ.map e).rnDeriv μ z))

theorem acceptanceFlow_le (μ : Measure Z) (e : Z ≃ᵐ Z) : acceptanceFlow μ e ≤ μ := by
  calc
    _ ≤ μ.withDensity 1 := withDensity_mono (Eventually.of_forall (fun z => min_le_left _ _))
    _ = μ := withDensity_one

instance acceptanceFlow_finite (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z) :
    IsFiniteMeasure (acceptanceFlow μ e) := isFiniteMeasure_of_le μ (acceptanceFlow_le μ e)

theorem acceptanceFlow_le_map (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z)
    (h : μ.map e ≪ μ) : acceptanceFlow μ e ≤ μ.map e := by
  calc
    _ ≤ μ.withDensity ((μ.map e).rnDeriv μ) :=
      withDensity_mono (Eventually.of_forall (fun z => min_le_right _ _))
    _ = μ.map e := Measure.withDensity_rnDeriv_eq _ _ h



theorem acceptanceFlow_inverse_le (μ : Measure Z) [IsFiniteMeasure μ] (e : Z ≃ᵐ Z)
    (h : μ.map e ≪ μ) : (acceptanceFlow μ e).map e.symm ≤ μ := by
  calc
    _ ≤ (μ.map e).map e.symm := Measure.map_mono (acceptanceFlow_le_map μ e h) e.symm.measurable
    _ = μ := by rw [Measure.map_map e.symm.measurable e.measurable]; simp

/-- Directed accepted edge flow. -/
noncomputable def acceptedEdges (ν : Measure Z) (e : Z ≃ᵐ Z) : Measure (Z × Z) :=
  ν.map (fun z => (z, e.symm z))

/-- Complete the accepted flow and its reverse by diagonal mass. The
marginals are μ+μ. This avoids any arbitrary kernel choices. -/
noncomputable def completedCoupling (μ ν : Measure Z) (e : Z ≃ᵐ Z) : Measure (Z × Z) :=
  acceptedEdges ν e + (acceptedEdges ν e).map Prod.swap +
    ((μ + μ) - (ν + ν.map e.symm)).map (fun z => (z, z))

theorem acceptedEdges_fst (ν : Measure Z) (e : Z ≃ᵐ Z) :
    (acceptedEdges ν e).map Prod.fst = ν := by
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) := measurable_id.prodMk e.symm.measurable
  rw [acceptedEdges, Measure.map_map measurable_fst hgraph]
  exact Measure.map_id

theorem acceptedEdges_snd (ν : Measure Z) (e : Z ≃ᵐ Z) :
    (acceptedEdges ν e).map Prod.snd = ν.map e.symm := by
  have hgraph : Measurable (fun z : Z => (z, e.symm z)) := measurable_id.prodMk e.symm.measurable
  rw [acceptedEdges, Measure.map_map measurable_snd hgraph]
  rfl

theorem completedCoupling_marginals (μ ν : Measure Z)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : Z ≃ᵐ Z)
    (hν : ν ≤ μ) (hνinv : ν.map e.symm ≤ μ) :
    (completedCoupling μ ν e).map Prod.fst = μ + μ ∧
      (completedCoupling μ ν e).map Prod.snd = μ + μ := by
  let A := acceptedEdges ν e
  let R := (μ + μ) - (ν + ν.map e.symm)
  have hsum : ν + ν.map e.symm ≤ μ + μ := add_le_add hν hνinv
  have hR : R + (ν + ν.map e.symm) = μ + μ := Measure.sub_add_cancel_of_le hsum
  have hA1 : A.map Prod.fst = ν := acceptedEdges_fst ν e
  have hA2 : A.map Prod.snd = ν.map e.symm := acceptedEdges_snd ν e
  have hAS1 : (A.map Prod.swap).map Prod.fst = ν.map e.symm := by
    rw [Measure.map_map measurable_fst measurable_swap]
    exact hA2
  have hAS2 : (A.map Prod.swap).map Prod.snd = ν := by
    rw [Measure.map_map measurable_snd measurable_swap]
    exact hA1
  have hdiag : Measurable (fun z : Z => (z,z)) := measurable_id.prodMk measurable_id
  have hR1 : (R.map (fun z => (z,z))).map Prod.fst = R := by
    rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  have hR2 : (R.map (fun z => (z,z))).map Prod.snd = R := by
    rw [Measure.map_map measurable_snd hdiag]
    exact Measure.map_id
  constructor
  · change (A + A.map Prod.swap + R.map (fun z => (z,z))).map Prod.fst = μ + μ
    rw [Measure.map_add _ _ measurable_fst, Measure.map_add _ _ measurable_fst, hA1, hAS1, hR1]
    exact (add_comm _ _).trans hR
  · change (A + A.map Prod.swap + R.map (fun z => (z,z))).map Prod.snd = μ + μ
    rw [Measure.map_add _ _ measurable_snd, Measure.map_add _ _ measurable_snd, hA2, hAS2, hR2]
    calc
      ν.map e.symm + ν + R = R + (ν + ν.map e.symm) := by ac_rfl
      _ = μ + μ := hR









end MeasureEquivalenceMarkov


