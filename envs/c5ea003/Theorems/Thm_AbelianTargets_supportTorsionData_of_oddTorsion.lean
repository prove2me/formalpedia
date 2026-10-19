-- Prove2me | Theorems.Thm_AbelianTargets_supportTorsionData_of_oddTorsion
-- name    : AbelianTargets.supportTorsionData_of_oddTorsion
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:53:13.04669+00:00
-- url     : https://prove2.me/theorems/66931046-6866-4f0c-90dc-54f4df90c378
-- title:
--   Odd reduced torsion supplies swapped generator paths and a filled relation
-- statement:
--   Let $H$ be a simple graph on a finite set $V$. Suppose some odd-length closed walk $\gamma$ has a positive power $\gamma^N$ reduced-homotopic to the empty walk. Then there exist $p\in\mathcal S(H)$, continuous paths $\alpha:p\to\tau p$ and $\beta:\tau p\to p$, and $k\in\mathbb N$ with $k>0$ such that
--   $$
--   \beta(t)=\tau(\alpha(t))\quad(t\in I),\qquad(\alpha*\beta)^k\simeq\operatorname{const}_p
--   $$
--   relative to the endpoints. Here $\mathcal S(H)$ is the space of pairs of probability masses with completely adjacent positive supports, and $\tau$ interchanges the two masses.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 6–7, especially Lemma 6.2 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/SupportWitness.lean, lines 86–108; SHA256 e9e09b97cd0dfde8b36ee2a591e1348e436b593b7ceb7722de1e022cd0a88601.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ProbabilityMap
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportWitness
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
# Support-space data from an arbitrary odd torsion target

This file removes the intermediate total-neighbor-choice hypothesis.
Every finite graph satisfying the actual odd torsion condition supplies
the two swapped paths and a nullhomotopy of their alternating power.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] (H : SimpleGraph V)

theorem AbelianTargets.supportTorsionData_of_oddTorsion (hH : HasOddTorsion H) :
    Nonempty (SupportTorsionData H) := by sorry
