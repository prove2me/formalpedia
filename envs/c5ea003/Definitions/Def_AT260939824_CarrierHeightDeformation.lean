-- Prove2me | Definitions.Def_AT260939824_CarrierHeightDeformation
-- name    : AT260939824_CarrierHeightDeformation
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:21:39.952738+00:00
-- url     : https://prove2.me/theorems/626e60a2-9b01-4b22-891d-beca2c0aa102
-- title:
--   The assembled height-zero deformation
-- statement:
--   Fix base $m\ge1$, height $K$, and integer interval $[A,B]$. The height-deformation map assembles the carrier's height chain into one time interval. It starts at the identity, fixes every distribution already supported at height zero, and ends at a distribution satisfying
--
--   $$ p_1(v)>0\ \Longrightarrow\ h(v)=0. $$
--
--   The terminal-value interface identifies this endpoint with the final state of the chain. These identities are used before contracting the resulting bottom interval.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/CarrierHeightDeformation.lean, selected declaration lines 10-12, 27-31, 33-43, 45-49, 51-54; SHA-256 9c1e349ae1d5fc1c216a0a3585e74429b59d6341f51ef28a83c142452d4ee05d. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierHeightChain
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_CurveFamilyStages
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_LowerCarrierCollapse
import Definitions.Def_AT260939824_OneHeightDeformation
import Definitions.Def_AT260939824_ParallelCollapse
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SimplicialSupport
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_TriangleCollapse
import Definitions.Def_AT260939824_UpperCarrierCollapse
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

/-! The actual finite strip is deformed to its literal bottom edges in
logarithmic-height time, with a speed independent of its horizontal size. -/

namespace AbelianTargets.IntervalCarriers
open scoped NNReal
noncomputable section

def heightDeformation {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (A B : ℤ)
    (z : Realization m K A B × unitInterval) : Realization m K A B :=
  familyHomotopy (heightChain hm K A B).curve K z







@[simp] theorem heightDeformation_zero {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) : heightDeformation hm K A B (p,0)=p := by
  unfold heightDeformation familyHomotopy
  change familyCurve (heightChain hm K A B).curve K (0,p)=p
  rw [familyCurve_zero,(heightChain hm K A B).initial]

theorem heightDeformation_one {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) :
    heightDeformation hm K A B (p,1)=(heightChain hm K A B).curve K (p,0) := by
  cases K with
  | zero =>
    unfold heightDeformation familyHomotopy familyCurve
    rfl
  | succ K =>
    unfold heightDeformation familyHomotopy
    change familyCurve (heightChain hm (K+1) A B).curve (K+1) (1,p)=_
    rw [familyCurve_one,(heightChain hm (K+1) A B).seam]

theorem heightDeformation_terminal {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) (v : CarrierVertex K A B)
    (hv : 0 < (heightDeformation hm K A B (p,1)).1.mass v) : v.1.2=0 := by
  rw [heightDeformation_one] at hv
  exact (heightChain hm K A B).terminal p v hv

theorem heightDeformation_fixes_bottom {m K : ℕ} {A B : ℤ} (hm : 1 ≤ m)
    (p : Realization m K A B) (hp : ∀ v,0 < p.1.mass v → v.1.2=0)
    (t : unitInterval) : heightDeformation hm K A B (p,t)=p :=
  familyCurve_fixed _ p p ((heightChain hm K A B).fixes_bottom p hp) K t

end
end AbelianTargets.IntervalCarriers


