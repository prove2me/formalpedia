-- Prove2me | solution 1 for MeasureEquivalenceRestrictedProduct.measurePreserving_sumTailEquiv
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:35:58.075627+00:00
-- url     : https://prove2.me/submissions/7cc52733-750d-4723-a1f3-f2844bf5f608

import Definitions.Def_BenchmarkOperator20261026_RationalFiberErgodic
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.CompactOpen
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

open MeasureTheory Set Filter
open scoped Topology
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
open MeasureEquivalenceRestrictedProduct

theorem solution (n : ℕ) :
    MeasurePreserving (sumTailEquiv n) (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  let shear : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) := fun z =>
    (z.1, z.2 + ∑ i, z.1 i)
  have hsplit : MeasurePreserving split (volume : Measure (Fin (n + 1) → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hs1 : MeasurePreserving Prod.swap
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) := Measure.measurePreserving_swap
  have hs2 : MeasurePreserving Prod.swap
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := Measure.measurePreserving_swap
  have hshear : MeasurePreserving shear
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure (Fin n → ℝ))).skew_product
      (g := fun y t => t + ∑ i, y i) (by fun_prop)
      (ae_of_all _ (fun y => map_add_right_eq_self volume (∑ i, y i)))
  have hc := hs2.comp (hshear.comp (hs1.comp hsplit))
  have he : (Prod.swap ∘ shear ∘ Prod.swap ∘ split) = sumTailEquiv n := by
    funext x
    apply Prod.ext
    · simp [Function.comp_def, shear, split, sumTailEquiv,
        MeasurableEquiv.piFinSuccAbove, Fin.sum_univ_succ, Fin.tail]
    · simp [Function.comp_def, shear, split, sumTailEquiv,
        MeasurableEquiv.piFinSuccAbove, Fin.tail]
      rfl
  rw [he] at hc
  exact hc
