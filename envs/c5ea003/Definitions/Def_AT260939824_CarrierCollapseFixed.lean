-- Prove2me | Definitions.Def_AT260939824_CarrierCollapseFixed
-- name    : AT260939824_CarrierCollapseFixed
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:17:04.364302+00:00
-- url     : https://prove2.me/theorems/e676872f-5a3d-4857-b5e2-6b944ef8feb2
-- title:
--   Lower-support fixed points of carrier collapses
-- statement:
--   Consider probability masses on the vertices of a carrier of height $K+1$. If every positive-mass vertex has height at most $K$, then the mass at every height-$K+1$ vertex is zero. The selected top, fan, and vertical collapse maps fix such a probability distribution at every time.
--
--   These invariants ensure that lowering the top layer leaves the existing lower carrier unchanged.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierCollapseFixed.lean, selected declaration lines 8-15, 17-23, 25-31, 33-38; SHA-256 db71bb3e899a51d9548b30cd7e796ec87b023e5acdbf2371648881a9a4f1a8de. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_LowerCarrierFaces
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ProbabilityPushGeometry
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
import Definitions.Def_AT260939824_UpperCarrierFaces
import Definitions.Def_AT260939824_VerticalCarrierCollapse
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
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

set_option backward.isDefEq.respectTransparency false

namespace AbelianTargets.IntervalCarriers
noncomputable section

theorem mass_zero_at_top {K : ℕ} {A B : ℤ} (p : Probability (CarrierVertex (K+1) A B))
    (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K) (v : CarrierVertex (K+1) A B) (hv : v.1.2 = K+1) :
    p.mass v = 0 := by
  apply le_antisymm _ (p.nonneg v)
  apply le_of_not_gt
  intro h
  have hh := hp v h
  omega

theorem top_mapList_fixes_lower {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (l : List (TopCell m K A B)) (t : unitInterval) : (topCollapseFamily hm).mapList l p t = p := by
  apply FreeCollapseFamily.mapList_fixes
  intro c hc
  exact Or.inl (mass_zero_at_top p hp (topTriangle hm c).a (by
    simp only [topTriangle,upperLeft,topCell_height c]))

theorem fan_mapList_fixes_lower {m K n : ℕ} {A B : ℤ} (hm : 1 ≤ m) (hn : n < m)
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (l : List (TopCell m K A B)) (t : unitInterval) : (fanCollapseFamily hm hn).mapList l p t = p := by
  apply FreeCollapseFamily.mapList_fixes
  intro c hc
  exact Or.inl (mass_zero_at_top p hp (fanTriangle hm hn c).a (by
    simp only [fanTriangle,upperLeft,topCell_height c]))

theorem verticalMap_fixes_lower {K : ℕ} {A B : ℤ}
    (p : Probability (CarrierVertex (K+1) A B)) (hp : ∀ v, 0 < p.mass v → v.1.2 ≤ K)
    (t : unitInterval) : verticalMap p t = p := by
  unfold verticalMap
  rw [Probability.push_eq_self floorVertex p (fun v hv => floorVertex_eq_self v (hp v hv))]
  exact Probability.mix_self _ _

end
end AbelianTargets.IntervalCarriers


