-- Prove2me | Definitions.Def_AT260939824_BottomIntervalMap
-- name    : AT260939824_BottomIntervalMap
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:10:13.031043+00:00
-- url     : https://prove2.me/theorems/771cb565-85c4-4843-9d25-d1cd44a6ce81
-- title:
--   Piecewise affine bottom-interval mass map
-- statement:
--   For the carrier over $[0,R]$ with height bound $K$, let $\delta_n$ denote the Dirac mass at the bottom vertex $(n,0)$, using the designated base as the total fallback outside the vertex range. The bottom mass map joins consecutive such masses affinely. On $[n,n+1]$ with $0\le n<R$, its value is
--
--   $$ (1-t)\delta_n+t\delta_{n+1},\qquad 0\le t\le1. $$
--
--   This provides the ambient coordinate representation of the bottom interval.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 4; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/BottomIntervalMap.lean, selected declaration lines 9-10, 12-15, 24-30; SHA-256 8650f1e4a58041e9e228aef78a6c79fdefd688be78834d2a8d87293eae4ef10b. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierRowRealization
import Definitions.Def_AT260939824_CompressedCarrierWalks
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
import Definitions.Def_AT260939824_FiniteIntervalGluing
import Definitions.Def_AT260939824_FixedSlotInterpolation
import Definitions.Def_AT260939824_IntervalCarriers
import Definitions.Def_AT260939824_JointCarrierRows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_RectangleHalfGluing
import Definitions.Def_AT260939824_RelativePathContraction
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_VariableRowFamilies
import Definitions.Def_AT260939824_WordPathHelpers
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
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
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

/-! The literal affine bottom interval in barycentric carrier coordinates. -/

namespace AbelianTargets.IntervalCarriers
noncomputable section

def bottomMass (K R n : ℕ) : CarrierVertex K 0 R → ℝ :=
  vertexMass (carrierBase K R) ((n : ℤ),0)

def bottomMap (K R : ℕ) (u : ℝ) : CarrierVertex K 0 R → ℝ :=
  FixedSlots.intervalGlue
    (fun n z => FixedSlots.mix (bottomMass K R n) (bottomMass K R (n+1)) z.1)
    (R-1) (u,0)



theorem bottomMass_eq (K R n : ℕ) (hn : n ≤ R) :
    bottomMass K R n = (Probability.dirac (bottomVertex K R n hn)).mass := by
  unfold bottomMass vertexMass
  have he : liftVertex (carrierBase K R) ((n : ℤ),0) = bottomVertex K R n hn := by
    apply Subtype.ext
    exact liftVertex_val _ _ (bottomVertex K R n hn).property
  rw [he]







end
end AbelianTargets.IntervalCarriers


