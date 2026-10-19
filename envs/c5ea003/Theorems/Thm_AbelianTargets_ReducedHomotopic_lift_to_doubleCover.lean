-- Prove2me | Theorems.Thm_AbelianTargets_ReducedHomotopic_lift_to_doubleCover
-- name    : AbelianTargets.ReducedHomotopic.lift_to_doubleCover
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:48:11.978508+00:00
-- url     : https://prove2.me/theorems/210f6ec3-b385-403c-b8ae-2a1a7f01dd57
-- title:
--   Reduced graph homotopies lift to the bipartite double cover
-- statement:
--   Let $H$ be a simple graph on an arbitrary set $V$, let $p,q$ be walks from $a$ to $b$, and suppose $p$ and $q$ are reduced-homotopic: they are related by the equivalence and concatenation closure of spur cancellation and removal of closed walks of length four. For either initial sheet $\sigma\in\{0,1\}$, lift a walk to the bipartite double cover by switching sheets at each edge. There are equalities of the lifted endpoints such that, after transporting the endpoints along these equalities,
--   $$\operatorname{lift}_\sigma(p)\simeq_{\mathrm{red}}\operatorname{lift}_\sigma(q).$$
--   The ending sheet is $\sigma+|p|\pmod2$ for $p$ and $\sigma+|q|\pmod2$ for $q$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 6–7, especially Lemma 6.2 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/DoubleCoverLifts.lean, lines 140–167; SHA256 4311ba9768820c9fa97996e3bf22ab1083a0785c1abf4704e0e9ae338e35fa1f.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_TopologicalWalks
import Definitions.Def_AbelianTargets260939824ReducedWalks
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

theorem AbelianTargets.ReducedHomotopic.lift_to_doubleCover {a b : V} {p q : H.Walk a b}
    (hpq : ReducedHomotopic H p q) (σ : Bool) :
    HeteroReducedHomotopic H.bipartiteDoubleCover (liftWalk H p σ) (liftWalk H q σ) := by sorry
