-- Prove2me | Theorems.Thm_AbelianTargets_oddSupportPath_torsion
-- name    : AbelianTargets.oddSupportPath_torsion
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:53:06.613487+00:00
-- url     : https://prove2.me/theorems/24b2f6ae-1b02-43ec-b122-82035d3b6a1c
-- title:
--   An odd reduced-torsion walk gives a null power of an alternating support loop
-- statement:
--   Let $H$ be a simple graph on a finite set $V$, and choose a neighbor $s(v)$ of every vertex. Let $\gamma$ be an odd-length closed walk at $a$. Suppose $\gamma^N$ is reduced-homotopic to the empty walk for some $N\in\mathbb N$, allowing $N=0$. Let $p=(\delta_a,\delta_{s(a)})\in\mathcal S(H)$, let $\alpha:p\to\tau p$ be the support-space realization of its lift from sheet zero, and let $\tau\alpha:\tau p\to p$ be the swapped return path. Then
--   $$
--   \exists k\in\mathbb N,\quad N=2k\quad\text{and}\quad(\alpha*(\tau\alpha))^k\simeq\operatorname{const}_p
--   $$
--   by a homotopy fixing both endpoints.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 6–7, especially Lemma 6.2 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/SupportTorsion.lean, lines 171–189; SHA256 bc56ae188a2ab135f302fa89006df5a041dd53f1baff9e1aeb3889a6ad3739a9.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_DoubleCoverLifts
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportGeometry
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AT260939824_SupportPathClasses
import Definitions.Def_AT260939824_SupportTorsion
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
# Odd torsion walks and support-space paths

This file makes the endpoint transports in the path-lifting argument of
Lemma 6.2 and Proposition 7.1 explicit.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [TopologicalSpace X]
variable {V : Type*} [Fintype V] (H : SimpleGraph V) (s : V → V) (hs : ∀ v, H.Adj v (s v))

theorem AbelianTargets.oddSupportPath_torsion {a : V} (γ : H.Walk a a) (hodd : Odd γ.length)
    {N : ℕ} (hnull : ReducedHomotopic H (loopPower H γ N) .nil) :
    ∃ k : ℕ, N = 2*k ∧
      (pathLoopPower (alternatingSupportLoop H (oddSupportPath H s hs γ hodd)) k).Homotopic
        (Path.refl (SupportPair.vertex H (hs a))) := by sorry
