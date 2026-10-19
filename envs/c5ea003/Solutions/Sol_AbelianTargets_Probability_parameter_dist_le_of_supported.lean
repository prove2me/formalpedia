-- Prove2me | solution 1 for AbelianTargets.Probability.parameter_dist_le_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:04:56.003721+00:00
-- url     : https://prove2.me/submissions/110f1608-f3b1-4119-92c3-46f2941849e7

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
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityParameters
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SegmentedOddPath
import Definitions.Def_AT260939824_SimplicialChartGluing
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
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

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.SimplexMetricGluing
section
/-!
# A common-face estimate for finite probability simplices

Two nearby probability points have a normalized coordinatewise minimum
supported in both of their support sets. This quantitative fact permits
Lipschitz estimates on simplex charts to be glued without an intrinsic-metric
assumption. The image diameter handles pairs with disjoint supports.
-/

namespace AbelianTargets

open scoped BigOperators NNReal

noncomputable section

namespace Probability

variable {V : Type*} [Fintype V]







theorem mass_dist_le (p q : Probability V) (v : V) :
    |p.mass v - q.mass v| ≤ dist p q := by
  exact (dist_le_pi_dist p.mass q.mass v)













end Probability





end

end AbelianTargets

end

/-! Affine chart coordinates have a bound depending only on face dimension. -/
namespace AbelianTargets.Probability
end AbelianTargets.Probability
open AbelianTargets
open AbelianTargets.Probability
open scoped BigOperators NNReal unitInterval
variable {V : Type*} [Fintype V]

theorem solution (c : V → I) (s : Finset V) (p q : Probability V)
    (hp : p.SupportedOn (s : Set V)) (hq : q.SupportedOn (s : Set V)) :
    dist (parameter c p) (parameter c q)≤(s.card : ℝ)*dist p q := by
  classical
  have he : (∑ v,(p.mass v-q.mass v)*(c v : ℝ))=∑ v∈s,(p.mass v-q.mass v)*(c v : ℝ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro v hv hvs
    rw [(supportedOn_iff_zero.mp hp) v hvs,(supportedOn_iff_zero.mp hq) v hvs]
    ring
  change |(∑ v,p.mass v*(c v : ℝ))-(∑ v,q.mass v*(c v : ℝ))|≤_
  rw [←Finset.sum_sub_distrib]
  simp_rw [←sub_mul]
  rw [he]
  calc
    _ ≤ ∑ v∈s,|(p.mass v-q.mass v)*(c v : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v∈s,dist p q := Finset.sum_le_sum (fun v hv => by
      rw [abs_mul,abs_of_nonneg (c v).property.1]
      have hd : |p.mass v-q.mass v|≤dist p q := by
        simpa only [Real.dist_eq] using mass_dist_le p q v
      calc
        _ ≤ |p.mass v-q.mass v| * 1 := mul_le_mul_of_nonneg_left (c v).property.2 (abs_nonneg _)
        _ ≤ dist p q := by simpa using hd)
    _ = _ := by simp
