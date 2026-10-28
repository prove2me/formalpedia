-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
-- name    : BenchmarkOperator20261026_OperatorStrongUnitary
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:30:23.196126+00:00
-- url     : https://prove2.me/theorems/2e639adb-3dab-413a-a94f-74d94588907d
-- title:
--   Operator Strong Unitary
-- statement:
--   Defines the unitary group as surjective complex-linear isometries and equips it with pointwise norm convergence on vectors. The retained structure and evaluation-continuity facts describe this strong topology. It is the unitary group used by the operator-coding construction.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorStrongUnitary.lean, lines 17–78; source SHA-256 7b39edff9a9c795f906091c2eab7be7395c73ee87c90e822eede3c6d212b10be. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
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

/-!
The strong topology on the actual group of unitary operators.  A unitary is
represented by a surjective complex-linear isometry; the induced topology is
pointwise norm convergence on vectors, not the operator-norm topology.
-/

open Filter Topology

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev StrongUnitary := H ≃ₗᵢ[ℂ] H

instance _root_.OperatorCoding.instTopologicalSpaceStrongUnitary : TopologicalSpace (StrongUnitary H) :=
  TopologicalSpace.induced (fun u : StrongUnitary H => (u : H → H)) inferInstance

variable {H}

theorem strongUnitary_continuous_eval (x : H) :
    Continuous (fun u : StrongUnitary H => u x) :=
  (continuous_apply x).comp continuous_induced_dom

theorem strongUnitary_continuous_iff {α : Type*} [TopologicalSpace α]
    (f : α → StrongUnitary H) :
    Continuous f ↔ ∀ x, Continuous (fun a => f a x) := by
  constructor
  · intro h x
    exact (strongUnitary_continuous_eval x).comp h
  · intro h
    exact continuous_induced_rng.mpr (continuous_pi h)

theorem strongUnitary_continuous_action {α : Type*} [TopologicalSpace α]
    {u : α → StrongUnitary H} {x : α → H} (hu : Continuous u) (hx : Continuous x) :
    Continuous (fun a => u a (x a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun b => dist (x b) (x a)) (𝓝 a) (𝓝 0) := by
    simpa using (hx.dist (continuous_const (y := x a))).tendsto a
  have h₂ : Tendsto (fun b => dist (u b (x a)) (u a (x a))) (𝓝 a) (𝓝 0) := by
    simpa using (((strongUnitary_continuous_eval (x a)).comp hu).dist
      (continuous_const (y := u a (x a)))).tendsto a
  apply squeeze_zero (fun b => dist_nonneg) (fun b => ?_) (by simpa using h₁.add h₂)
  calc
    dist (u b (x b)) (u a (x a)) ≤
        dist (u b (x b)) (u b (x a)) + dist (u b (x a)) (u a (x a)) := dist_triangle _ _ _
    _ = dist (x b) (x a) + dist (u b (x a)) (u a (x a)) := by
      congr 1
      exact (u b).toIsometryEquiv.dist_eq _ _

instance strongUnitary_topologicalGroup : IsTopologicalGroup (StrongUnitary H) where
  continuous_mul := by
    apply (strongUnitary_continuous_iff _).mpr
    intro x
    change Continuous (fun p : StrongUnitary H × StrongUnitary H => p.1 (p.2 x))
    exact strongUnitary_continuous_action
      (u := fun p : StrongUnitary H × StrongUnitary H => p.1)
      (x := fun p : StrongUnitary H × StrongUnitary H => p.2 x) continuous_fst
      ((strongUnitary_continuous_eval x).comp continuous_snd)
  continuous_inv := by
    apply (strongUnitary_continuous_iff _).mpr
    intro x
    rw [continuous_iff_continuousAt]
    intro u₀
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h : Tendsto (fun u : StrongUnitary H => dist x (u (u₀⁻¹ x))) (𝓝 u₀) (𝓝 0) := by
      simpa using ((continuous_const (y := x)).dist
        (strongUnitary_continuous_eval (u₀⁻¹ x))).tendsto u₀
    convert h using 1
    funext u
    change dist ((u : H ≃ₗᵢ[ℂ] H).symm x) ((u₀ : H ≃ₗᵢ[ℂ] H).symm x) = _
    rw [← u.toIsometryEquiv.dist_eq]
    simp





end OperatorCoding


