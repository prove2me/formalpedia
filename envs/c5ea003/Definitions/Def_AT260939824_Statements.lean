-- Prove2me | Definitions.Def_AT260939824_Statements
-- name    : AT260939824_Statements
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T03:24:36.704225+00:00
-- url     : https://prove2.me/theorems/60627311-55f4-4c2c-921c-00cf49e4ee4e
-- title:
--   The two universal-target statement predicates
-- statement:
--   Let $H$ be a finite graph whose vertex type has the discrete topology. The first statement predicate says that the existence of an odd closed walk whose square is homotopic to the trivial walk implies that $H$ is a universal target for every lattice dimension $d\ge1$. This is the hypothesis of Theorem 1.4.
--
--   The second predicate replaces the square by an arbitrary positive power under the paper's reduced-walk homotopy, giving the positive finite-order hypothesis of Proposition 7.1. In both predicates, universal target quantifies over all free continuous lattice actions on zero-dimensional Polish spaces in the chosen universe and asserts existence of a continuous graph homomorphism to $H$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 1 (Theorem 1.4), 2, 7.1 (Proposition 7.1); https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization; its implementation definitions are not asserted to be separately numbered in the paper. Original Lean module AbelianTargets/Statements.lean, selected declaration lines 22-24, 26-28; SHA-256 f33f32d840068b441be3556214e5613f00f09e045848ee415d751e0438a07a85. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerWindows
import Definitions.Def_AT260939824_Probability
import Definitions.Def_AT260939824_ReducedWalks
import Definitions.Def_AT260939824_Rounding
import Definitions.Def_AT260939824_SupportModel
import Definitions.Def_AbelianTargets260939824Actions
import Definitions.Def_AbelianTargets260939824ReducedWalks
import Init
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.Transitive
import Mathlib.GroupTheory.OrderOfElement
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
# Exact requested statements and intermediate construction interfaces

`Theorem14Statement` and `Proposition71Statement` give the exact requested
positive propositions. Their unconditional proofs in every positive dimension
are `theorem1_4` and `proposition7_1` in `PositiveTheorems.lean`.
The intermediate construction interface and conditional closing implications
below are retained as reusable APIs.
-/

namespace AbelianTargets

universe u v

variable {V : Type v} [TopologicalSpace V]

/-- Theorem 1.4, with the paper's exact reduced-walk hypothesis. -/
def Theorem14Statement (H : SimpleGraph V) [Fintype V] [DiscreteTopology V] : Prop :=
  HasOddInvolution H → ∀ d : ℕ, 1 ≤ d → UniversalTarget.{u} d H

/-- Proposition 7.1, with the paper's exact positive finite-order hypothesis. -/
def Proposition71Statement (H : SimpleGraph V) [Fintype V] [DiscreteTopology V] : Prop :=
  HasOddTorsion H → ∀ d : ℕ, 1 ≤ d → UniversalTarget.{u} d H











end AbelianTargets


