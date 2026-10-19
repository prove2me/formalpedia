-- Prove2me | Theorems.Thm_AbelianTargets_probabilityField_of_approximateParityMaps
-- name    : AbelianTargets.probabilityField_of_approximateParityMaps
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:53:19.846986+00:00
-- url     : https://prove2.me/theorems/56c9c9b6-1d2d-4232-aff1-2a08c112403d
-- title:
--   A probability field from compact support data and approximate parity maps
-- statement:
--   Let $d\in\mathbb N$, let $X$ be a topological space carrying a $\mathbb Z^d$-action, let $Y$ be a compact metric space, and let $V$ be a nonempty finite set. Let $H$ be a simple graph on $V$ and $\tau:Y\to Y$ any function. Suppose $p,q:Y\to\Delta(V)$ satisfy: $p$ is continuous, the supports of $p_y$ and $q_y$ are completely adjacent in $H$, and
--   $$
--   p_{\tau y}=q_y.
--   $$
--   Assume that for every $\varepsilon>0$ there is a continuous finite-image $f:X\to Y$ with
--   $$
--   d\bigl(f(e_i\cdot x),\tau f(x)\bigr)<\varepsilon
--   \qquad\text{for every }x,i.
--   $$
--   Then there exist $P,Q:X\to\Delta(V)$ with $P$ continuous and finite-image, completely adjacent supports at each $x$, and
--   $$
--   |P_{e_i\cdot x}(v)-Q_x(v)|<\frac1{2|V|}
--   \qquad\text{for every }x,i,v.
--   $$
--   No involution, isometry, or continuity assumption on $\tau$ is imposed.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 6, Proposition 6.1 and the closing argument for Theorem 1.4; https://arxiv.org/html/2609.39824v1#S6. Auxiliary formalization result in original module AbelianTargets/SupportModel.lean, authoritative declaration span lines 35-66, SHA-256 a08106238ed36657e7cbfa18beceaf4b4c73df65936692a02ac81f08b9a4283c. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false

/-!
# The analytic implication in Section 6

This file checks composition with an equivariant support model, choice of
a uniform error on a compact source, and exact graph rounding.
The actual presentation complex is constructed in separate modules;
existence of its approximate parity maps remains an explicit geometric input.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets

theorem AbelianTargets.probabilityField_of_approximateParityMaps
    {d : ℕ} {X Y V : Type*} [TopologicalSpace X]
    [AddAction (Lattice d) X] [MetricSpace Y] [CompactSpace Y]
    [Fintype V] [Nonempty V] {H : SimpleGraph V} {τ : Y → Y}
    (model : SupportModel H τ)
    (approx : ApproximateParityMaps (d := d) X Y τ) :
    Nonempty (ProbabilityField (d := d) (X := X) H) := by sorry
