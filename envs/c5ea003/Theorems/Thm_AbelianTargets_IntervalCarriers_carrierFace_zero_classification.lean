-- Prove2me | Theorems.Thm_AbelianTargets_IntervalCarriers_carrierFace_zero_classification
-- name    : AbelianTargets.IntervalCarriers.carrierFace_zero_classification
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:43:07.209343+00:00
-- url     : https://prove2.me/theorems/f8280ae3-6188-42c7-beca-9684a7453344
-- title:
--   Classification of faces in a height-zero interval carrier
-- statement:
--   Let $m,R\in\mathbb N$ and let $s$ be a finite simplicial face of the interval carrier with parameter $m$, height zero, and horizontal interval $[0,R]$. Carrier vertices are pairs in $\mathbb Z\times\mathbb N$; at height zero they have the form $(n,0)$ with $0\le n\le R$. Then
--   $$
--   \left(\exists n\in\mathbb N,\ n\le R,\ s\subseteq\{(n,0)\}\right)
--   \ \lor\
--   \left(\exists n\in\mathbb N,\ n<R,\
--   s\subseteq\{(n,0),(n+1,0)\}\right).
--   $$
--   Thus each face is contained in a single bottom vertex or a consecutive bottom unit edge. The conclusion uses containment rather than equality and permits an empty face. No lower bound on $m$ is required, and $R=0$ leaves only the first alternative.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 4, bottom faces of finite carriers supporting Lemma 4.1; https://arxiv.org/html/2609.39824v1#S4. Auxiliary formalization result in original module AbelianTargets/BottomCarrierClassification.lean, authoritative declaration span lines 10-55, SHA-256 e7abb2c6b118101aa4ab4d49d324f9146c7a2b048ae8e8b4e3dd6765d3f5ddc2. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
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

theorem AbelianTargets.IntervalCarriers.carrierFace_zero_classification {m R : ℕ} {s : Finset Vertex}
    (hs : CarrierFace m 0 0 R s) :
    (∃ n : ℕ,n ≤ R ∧ s ⊆ {((n : ℤ),0)}) ∨
      ∃ n : ℕ,n < R ∧ s ⊆ {((n : ℤ),0),(((n+1 : ℕ) : ℤ),0)} := by sorry
