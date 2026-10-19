-- Prove2me | Definitions.Def_AbelianTargets260939824Actions
-- name    : AbelianTargets260939824Actions
-- status  : Definition
-- author  : @username
-- created : 2026-10-18T07:41:37.838195+00:00
-- url     : https://prove2.me/theorems/f8c44336-cf70-4ab5-a7c7-61a73cf56d6c
-- title:
--   Lattice actions and continuous graph homomorphisms
-- statement:
--   For each natural number $d$, let $L_d=\mathbb Z^{\mathrm{Fin}(d)}$. The standard generators $e_i$ have value one at $i$ and zero elsewhere. An action is free when $g\cdot x=x$ implies $g=0$, and a topological space is zero-dimensional when its clopen subsets form a basis. The standard Schreier relation joins $x$ and $y$ if $e_i\cdot x=y$ or $e_i\cdot y=x$ for some $i$.
--
--   For a topological simple graph $H$ on $V$, write $\operatorname{UniversalTarget}(d,H)$ if every free continuous $L_d$-action on every zero-dimensional Polish space $X$ admits a continuous map $c:X\to V$ carrying this relation to adjacency in $H$. This definition supplies the shared conclusion of the two target results; finiteness and discreteness of $V$ are imposed in the theorem statements.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Section 2.1; https://arxiv.org/html/2609.39824v1#S2.SS1

import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

/-!
The action and conclusion definitions for Theorem 1.4 and Proposition 7.1
of arXiv:2609.39824v1. A finite target vertex type receives its discrete
topology in the theorem statements. No mathematical result is assumed here.
-/

set_option autoImplicit false

namespace AbelianTargets

/-- The additive group of integer lattice displacements in dimension `d`. -/
abbrev Lattice (d : ℕ) := Fin d → ℤ

/-- The standard positive generator in coordinate `i`. -/
def unitVector {d : ℕ} (i : Fin d) : Lattice d :=
  fun j => if j = i then 1 else 0

/-- A lattice action is free if every point has trivial stabilizer. -/
def IsFree {G X : Type*} [AddGroup G] [AddAction G X] : Prop :=
  ∀ (g : G) (x : X), g +ᵥ x = x → g = 0

/-- A zero-dimensional space has a basis of clopen subsets. -/
def ZeroDimensional (X : Type*) [TopologicalSpace X] : Prop :=
  TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}

/-- Undirected standard Schreier adjacency for an additive lattice action. -/
def StandardEdge {d : ℕ} {X : Type*} [AddAction (Lattice d) X]
    (x y : X) : Prop :=
  ∃ i : Fin d, unitVector i +ᵥ x = y ∨ unitVector i +ᵥ y = x

/-- A continuous homomorphism from the standard Schreier graph to `H`. -/
def HasContinuousHom {d : ℕ} {X V : Type*}
    [AddAction (Lattice d) X] [TopologicalSpace X] [TopologicalSpace V]
    (H : SimpleGraph V) : Prop :=
  ∃ c : X → V, Continuous c ∧
    ∀ x y : X, StandardEdge (d := d) x y → H.Adj (c x) (c y)

/-- Every free continuous action on a zero-dimensional Polish space has a
continuous standard-Schreier-graph homomorphism to `H`. -/
def UniversalTarget.{u, v} (d : ℕ) {V : Type v} [TopologicalSpace V]
    (H : SimpleGraph V) : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [PolishSpace X]
    [AddAction (Lattice d) X] [ContinuousVAdd (Lattice d) X],
    ZeroDimensional X → IsFree (G := Lattice d) (X := X) →
      HasContinuousHom (d := d) (X := X) H

end AbelianTargets


