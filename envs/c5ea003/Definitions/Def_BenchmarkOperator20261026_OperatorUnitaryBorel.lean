-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorUnitaryBorel
-- name    : BenchmarkOperator20261026_OperatorUnitaryBorel
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:37:08.182659+00:00
-- url     : https://prove2.me/theorems/3447cd26-6b4d-49fe-91e2-79930f7bba12
-- title:
--   Operator Unitary Borel
-- statement:
--   Defines the topology induced by evaluating a unitary on one countable dense sequence of vectors. The retained comparison and evaluation facts identify it with the strong topology and establish second countability for the later Borel arguments.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorUnitaryBorel.lean, lines 13–59; source SHA-256 433d763295f31788e5c463f7413019221de81296a0d65b0f5d8c6e77d85a556a. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Semicontinuity.Basic

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

/-! The strong topology on the unitary group is determined by countably
many dense vector evaluations. This identifies its Borel structure without
using operator-norm measurability in place of strong measurability. -/

open Filter Topology TopologicalSpace

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]

noncomputable abbrev strongUnitaryDenseTopology : TopologicalSpace (StrongUnitary H) :=
  TopologicalSpace.induced (fun u : StrongUnitary H => fun n : ℕ => u (denseSeq H n)) inferInstance

variable {H}

theorem strongUnitary_denseEvaluation_continuous (x : H) :
    @Continuous (StrongUnitary H) H (strongUnitaryDenseTopology H) inferInstance (fun u => u x) := by
  letI : TopologicalSpace (StrongUnitary H) := strongUnitaryDenseTopology H
  apply continuous_iff_continuousAt.mpr
  intro U
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := (denseRange_denseSeq H).exists_dist_lt x (by positivity : (0 : ℝ) < ε / 3)
  have hmap : Continuous (fun V : StrongUnitary H => fun k : ℕ => V (denseSeq H k)) :=
    continuous_induced_dom
  have he : Continuous (fun V : StrongUnitary H => V (denseSeq H n)) :=
    (continuous_apply n).comp hmap
  have hv := Metric.continuousAt_iff'.mp (he.continuousAt (x := U)) (ε / 3) (by positivity)
  filter_upwards [hv] with V hV
  have h₁ := dist_triangle (V x) (V (denseSeq H n)) (U x)
  have h₂ := dist_triangle (V (denseSeq H n)) (U (denseSeq H n)) (U x)
  have hVnorm : dist (V x) (V (denseSeq H n)) = dist x (denseSeq H n) :=
    V.toIsometryEquiv.dist_eq _ _
  have hUnorm : dist (U (denseSeq H n)) (U x) = dist x (denseSeq H n) := by
    exact (U.toIsometryEquiv.dist_eq _ _).trans (dist_comm _ _)
  rw [hVnorm] at h₁
  rw [hUnorm] at h₂
  linarith

theorem strongUnitary_topology_eq_dense :
    instTopologicalSpaceStrongUnitary H = strongUnitaryDenseTopology H := by
  have hforward : @Continuous (StrongUnitary H) (StrongUnitary H)
      (instTopologicalSpaceStrongUnitary H) (strongUnitaryDenseTopology H) id := by
    apply continuous_induced_rng.mpr
    exact continuous_pi (fun n => strongUnitary_continuous_eval (denseSeq H n))
  have hbackward : @Continuous (StrongUnitary H) (StrongUnitary H)
      (strongUnitaryDenseTopology H) (instTopologicalSpaceStrongUnitary H) id := by
    exact (@strongUnitary_continuous_iff H _ _ (StrongUnitary H)
      (strongUnitaryDenseTopology H) id).mpr strongUnitary_denseEvaluation_continuous
  exact le_antisymm
    (by simpa only [induced_id] using continuous_iff_le_induced.mp hforward)
    (by simpa only [induced_id] using continuous_iff_le_induced.mp hbackward)

instance strongUnitary_secondCountable [SecondCountableTopology H] :
    SecondCountableTopology (StrongUnitary H) := by
  rw [strongUnitary_topology_eq_dense]
  exact secondCountableTopology_induced _ _ _





end OperatorCoding


