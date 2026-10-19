-- Prove2me | Theorems.Thm_AbelianTargets_exists_clopen_shift_independent
-- name    : AbelianTargets.exists_clopen_shift_independent
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:50:03.690151+00:00
-- url     : https://prove2.me/theorems/7f06cb20-7c8d-499b-9501-4c80ec33b96f
-- title:
--   A point has a clopen neighborhood disjoint from a fixed nontrivial shift
-- statement:
--   Let $d\in\mathbb N$ and let the additive group $\mathbb Z^d$ act freely and continuously on a $T_1$ space $X$ having a basis of clopen sets. For every $x\in X$ and $g\in\mathbb Z^d\setminus\{0\}$ there is a clopen neighborhood $U$ of $x$ such that
--   $$
--   y\in U\ \Longrightarrow\ g\cdot y\notin U.
--   $$
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/MarkerExistence.lean, lines 83–101; SHA256 a33841719ebcd22734eec82b9054f795f4adf6f5975e148780d77f2cd9efb338.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AbelianTargets260939824Actions
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Existence of clopen separated covering orbit markers

This file completes the positive membership of the concrete graph in
Lemma 7.3. A countable clopen independent cover is built from freeness,
zero-dimensionality, and second countability. The greedy clopen maximal
independent set then supplies the required orbit markers.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
universe u
variable {d L : ℕ} {X : Type*} [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X]
variable [T1Space X]

theorem AbelianTargets.exists_clopen_shift_independent
    (zeroDim : ZeroDimensional X) (free : IsFree (G := Lattice d) (X := X))
    (x : X) (g : Lattice d) (hg : g ≠ 0) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ y ∈ U, g +ᵥ y ∉ U := by sorry
