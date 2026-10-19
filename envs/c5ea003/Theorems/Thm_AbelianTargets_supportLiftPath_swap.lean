-- Prove2me | Theorems.Thm_AbelianTargets_supportLiftPath_swap
-- name    : AbelianTargets.supportLiftPath_swap
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:52:41.017835+00:00
-- url     : https://prove2.me/theorems/cbb3508f-cc74-4eb4-ad79-d98d81c5f805
-- title:
--   The support-space realization of a lifted walk commutes with shore swap
-- statement:
--   Let $H$ be a simple graph on a finite set $V$, and choose $s:V\to V$ with $v\sim_H s(v)$ for every $v$. Realize the bipartite double cover in the support space
--   $$\mathcal S(H)=\{(\mu,\nu):\mu,\nu\text{ probability masses on }V,\ \mu(v)>0,\nu(w)>0\Rightarrow v\sim_H w\}.$$
--   Let $\tau(\mu,\nu)=(\nu,\mu)$, and let $P_{p,\sigma}:I\to\mathcal S(H)$ be the support-space path obtained by realizing the lift of a graph walk $p:a\to b$ from sheet $\sigma$. Then
--   $$\tau(P_{p,\sigma}(t))=P_{p,1-\sigma}(t)\qquad(t\in I).$$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 6–7, especially Lemma 6.2 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/DoubleCoverLifts.lean, lines 213–227; SHA256 4311ba9768820c9fa97996e3bf22ab1083a0785c1abf4704e0e9ae338e35fa1f.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_DoubleCoverSupport
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_TopologicalWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

/-!
# Binary lifts of graph walks

Walks lift to the bipartite double cover with the sheet determined by their
length parity.  This is the combinatorial covering step in Lemma 6.2.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {V : Type*} (H : SimpleGraph V)
variable [Fintype V] (s : V → V) (hs : ∀ v, H.Adj v (s v))

set_option backward.isDefEq.respectTransparency false

theorem AbelianTargets.supportLiftPath_swap {a b : V} (p : H.Walk a b) (σ : Bool) (t : unitInterval) :
    SupportPair.swap H (supportLiftPath H s hs p σ t) = supportLiftPath H s hs p (!σ) t := by sorry
