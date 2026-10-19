-- Prove2me | Theorems.Thm_AbelianTargets_IntervalCarriers_bottomSupported_of_face
-- name    : AbelianTargets.IntervalCarriers.bottomSupported_of_face
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:43:08.821037+00:00
-- url     : https://prove2.me/theorems/f1b377e9-94b5-4a61-a1b7-494762e0827c
-- title:
--   Bottom support from a height-zero carrier face
-- statement:
--   Let $m,K,R\in\mathbb N$. Let $p$ be a probability distribution on the finite carrier vertices
--   $$
--   \{(a,h)\in\mathbb Z\times\mathbb N:0\le a\le R,\ h\le K\},
--   $$
--   and let $s$ be a finite subset of those vertices. Assume every vertex with positive $p$-mass belongs to $s$, and that the underlying coordinate pairs of $s$ form a simplicial face of the height-zero interval carrier with parameter $m$ over $[0,R]$. Then
--   $$
--   \left(\exists n\le R,\ \operatorname{supp}(p)\subseteq\{(n,0)\}\right)
--   \ \lor\
--   \left(\exists n<R,\
--   \operatorname{supp}(p)\subseteq\{(n,0),(n+1,0)\}\right),
--   $$
--   where $n$ ranges over natural numbers and the displayed bottom vertices are regarded as vertices of the height-$K$ carrier. This is the precise bottom-support property needed for the barycentric bottom-coordinate parametrization.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 4, bottom realization coordinates supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/BottomCarrierClassification.lean, authoritative declaration span lines 57-77, SHA-256 e7abb2c6b118101aa4ab4d49d324f9146c7a2b048ae8e8b4e3dd6765d3f5ddc2. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_BottomCoordinateInverse
import Definitions.Def_AT260939824_CarrierCellRealization
import Definitions.Def_AT260939824_CarrierFanMoves
import Definitions.Def_AT260939824_CarrierGeometry
import Definitions.Def_AT260939824_CarrierTriangulation
import Definitions.Def_AT260939824_CompressedWords
import Definitions.Def_AT260939824_DigitPathRealization
import Definitions.Def_AT260939824_EndpointCorrection
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

/-! Literal height-zero carrier faces are single vertices or adjacent
horizontal unit edges. Hence every bottom realization point is exactly
recovered from its barycentric horizontal coordinate. -/
namespace AbelianTargets.IntervalCarriers
end AbelianTargets.IntervalCarriers
open AbelianTargets
open AbelianTargets.IntervalCarriers

theorem AbelianTargets.IntervalCarriers.bottomSupported_of_face {m K R : ℕ}
    (p : Probability (CarrierVertex K 0 R)) (s : Finset (CarrierVertex K 0 R))
    (hs : CarrierFace m 0 0 R (s.image Subtype.val))
    (hp : p.SupportedOn (s : Set _)) : BottomSupported K R p := by sorry
