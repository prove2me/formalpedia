-- Prove2me | solution 1 for AbelianTargets.SupportTorsionData.affineChart_uniform_face_modulus
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:08:55.714867+00:00
-- url     : https://prove2.me/submissions/42021fd1-b84c-401a-bfc6-63fd200ad281

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomEdgeSplice
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_ParitySwapGeometry
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportRelationCharts
import Definitions.Def_AT260939824_SupportWitness
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Theorems.Thm_AbelianTargets_Probability_parameter_dist_le_of_supported

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.SupportGeometry
section
/-!
# Concrete probability support geometry

The space `SupportPair H` is the support space `𝒟(H)` in Lemma 6.2 of
arXiv:2609.39824.  Its shore swap is a free involution.  Convex interpolation
inside a fixed shore gives the graph-edge paths, and interpolation of both
shores gives the square filling for a four-walk.  These are actual continuous
maps, not assumptions about an auxiliary presentation complex.
-/

open scoped BigOperators unitInterval

namespace AbelianTargets

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]

attribute [local instance] Classical.propDecidable











































end Probability

variable {V : Type*} [Fintype V] (H : SimpleGraph V)















namespace SupportPair




























theorem isometry_swap : Isometry (swap H) := by
  apply Isometry.of_dist_eq
  intro z w
  change max (dist z.right w.right) (dist z.left w.left) =
    max (dist z.left w.left) (dist z.right w.right)
  exact max_comm _ _









































































end SupportPair

end

end AbelianTargets

end

-- Preserved source skeleton: AbelianTargets.UniformAffineSupportCharts
section
/-! A common modulus for all torsion charts, independent of the vertex set. -/
universe v
namespace AbelianTargets
noncomputable section
open scoped unitInterval
attribute [local instance] Classical.propDecidable

namespace SupportPair
theorem paritySwap_dist {W : Type*} [Fintype W] (H : SimpleGraph W) (r : ℤ)
    (p q : SupportPair H) : dist (paritySwap H r p) (paritySwap H r q)=dist p q := by
  unfold paritySwap
  split_ifs
  · rfl
  · exact (isometry_swap H).dist_eq _ _
end SupportPair

namespace Probability


end Probability

namespace SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)







end SupportTorsionData
end
end AbelianTargets

end

/-! A common modulus for all torsion charts, independent of the vertex set. -/
universe v
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped unitInterval
attribute [local instance] Classical.propDecidable
namespace AbelianTargets.SupportTorsionData
end AbelianTargets.SupportTorsionData
open AbelianTargets
open AbelianTargets.SupportTorsionData
variable {W : Type*} [Fintype W] {H : SimpleGraph W} (D : SupportTorsionData H)

theorem solution :
    ∀ ε:ℝ,0<ε→∃δ:ℝ,0<δ ∧
      ∀ {V:Type v} [Fintype V] (height theta:V→I) (r:ℤ) (s:Finset V)
        (p q:Probability V),s.card≤3→p.SupportedOn (s:Set V)→q.SupportedOn (s:Set V)→
        dist p q<δ→dist (SupportPair.paritySwap H r (D.affineChart height theta p))
          (SupportPair.paritySwap H r (D.affineChart height theta q))<ε := by
  intro ε hε
  have huc : UniformContinuous D.relationHomotopy :=
    CompactSpace.uniformContinuous_of_continuous D.relationHomotopy.continuous
  obtain ⟨η,hη,hbound⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨η/3,by positivity,?_⟩
  intro V inst height theta r s p q hcard hp hq hd
  rw [SupportPair.paritySwap_dist]
  apply hbound
  have h₁ := Probability.parameter_dist_le_of_supported height s p q hp hq
  have h₂ := Probability.parameter_dist_le_of_supported theta s p q hp hq
  have hc : (s.card:ℝ)≤3 := by exact_mod_cast hcard
  have hh : dist (Probability.parameter height p,Probability.parameter theta p)
      (Probability.parameter height q,Probability.parameter theta q)≤3*dist p q := by
    rw [Prod.dist_eq]
    exact max_le (h₁.trans (mul_le_mul_of_nonneg_right hc dist_nonneg))
      (h₂.trans (mul_le_mul_of_nonneg_right hc dist_nonneg))
  exact hh.trans_lt (by linarith)
