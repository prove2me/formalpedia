-- Prove2me | solution 1 for MeasureUnitary.measurable_nat_nth
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:27:42.504808+00:00
-- url     : https://prove2.me/submissions/400fddc6-ceac-4529-8e00-a190a9b8f0d3

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

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

-- Preserved source skeleton: MeasureGramSchmidtBorel
section
/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/

open MeasureTheory InnerProductSpace Set Finset

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]





theorem measurable_nat_count (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (n : ℕ) :
    Measurable (fun s => Nat.count (p s) n) := by
  induction n with
  | zero => simpa only [Nat.count_zero] using (measurable_const : Measurable (fun _ : S => (0 : ℕ)))
  | succ n ih =>
    simp_rw [Nat.count_succ]
    exact ih.add (Measurable.ite (hp n) measurable_const measurable_const)



















end MeasureUnitary

end

/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/
open MeasureTheory InnerProductSpace Set Finset
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary
variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem solution (p : S → ℕ → Prop) [∀ s, DecidablePred (p s)]
    (hp : ∀ n, MeasurableSet {s | p s n}) (hinf : ∀ s, {n | p s n}.Infinite) (n : ℕ) :
    Measurable (fun s => Nat.nth (p s) n) := by
  apply measurable_to_countable'
  intro m
  have heq : {s | Nat.nth (p s) n = m} = {s | p s m} ∩ {s | Nat.count (p s) m = n} := by
    ext s
    constructor
    · intro h
      exact ⟨h ▸ Nat.nth_mem_of_infinite (hinf s) n,
        h ▸ Nat.count_nth_of_infinite (hinf s) n⟩
    · rintro ⟨hm, hc⟩
      rw [← hc]
      exact Nat.nth_count hm
  change MeasurableSet {s | Nat.nth (p s) n = m}
  rw [heq]
  exact (hp m).inter (measurableSet_eq_fun (measurable_nat_count p hp m) measurable_const)
