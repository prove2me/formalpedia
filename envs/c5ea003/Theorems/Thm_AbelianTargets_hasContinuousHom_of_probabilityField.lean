-- Prove2me | Theorems.Thm_AbelianTargets_hasContinuousHom_of_probabilityField
-- name    : AbelianTargets.hasContinuousHom_of_probabilityField
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:52:49.867016+00:00
-- url     : https://prove2.me/theorems/b7172a1a-15eb-4c01-8901-cc3379141777
-- title:
--   Continuous graph rounding from a finite-image probability field
-- statement:
--   Let $d\in\mathbb N$, let $X$ be a topological space with an action of $\mathbb Z^d$, and let $V$ be a finite set with any topology. Let $H$ be a simple graph on $V$. Suppose $p,q:X\to\Delta(V)$ are probability distributions at each point, $p$ is continuous with finite image, and positive masses on their two shores are adjacent:
--   $$
--   p_x(v)>0,\ q_x(w)>0\Longrightarrow H.\operatorname{Adj}(v,w).
--   $$
--   Whenever $X$ is nonempty, its probability field forces $n=|V|>0$. Assume the coordinate error bound
--   $$
--   \left|p_{e_i\cdot x}(v)-q_x(v)\right|<\frac1{2n}
--   \qquad(x\in X,\ i\in\{1,\ldots,d\},\ v\in V).
--   $$
--   Then a continuous $c:X\to V$ takes every standard Schreier edge to an edge of $H$. No continuity of $q$, freeness, continuity of the action, or discreteness of $V$ is required. The empty-source case and $d=0$ are included.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 6, the closing probability-rounding argument for Theorem 1.4; https://arxiv.org/html/2609.39824v1#S6. Auxiliary formalization result in original module AbelianTargets/Rounding.lean, authoritative declaration span lines 42-63, SHA-256 c6f4d3914945f30a85748acd773b059f0eb10d8e43731909cc4911e70c910c0a. Frozen original source is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_Rounding
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
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Continuous finite-range rounding

The final step of Theorem 1.4 and Proposition 7.1 is proved here.
The existence of `ProbabilityField` is a separate, unproved geometric
obligation, never an axiom of this project.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets

theorem AbelianTargets.hasContinuousHom_of_probabilityField
    {d : ℕ} {X V : Type*} [AddAction (Lattice d) X]
    [TopologicalSpace X] [TopologicalSpace V] [Fintype V]
    {H : SimpleGraph V} (field : ProbabilityField (d := d) (X := X) H) :
    HasContinuousHom (d := d) (X := X) H := by sorry
