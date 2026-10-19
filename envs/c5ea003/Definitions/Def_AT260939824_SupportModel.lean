-- Prove2me | Definitions.Def_AT260939824_SupportModel
-- name    : AT260939824_SupportModel
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:42:14.956688+00:00
-- url     : https://prove2.me/theorems/facc07fb-4b42-4266-92c4-c290bc8f07b8
-- title:
--   Approximate parity maps and analytic support coordinates
-- statement:
--   Let $\mathbb Z^d$ act on a topological space $X$, let $Y$ be metric, and let $\tau:Y\to Y$ be any map. Approximate parity maps mean
--   $$\forall\varepsilon>0\ \exists f:X\to Y\text{ continuous with finite range},\quad
--   d(f(e_i\cdot x),\tau(f(x)))<\varepsilon\quad\forall x,i.$$
--   For a finite graph $H$, a support model on a topological $Y$ consists of probability-coordinate maps $p,q:Y\to\operatorname{Prob}(V(H))$ with $p$ continuous, completely adjacent positive supports at every point, and $p(\tau y)=q(y)$. Neither continuity of $q$ nor any involution condition on $\tau$ is part of this structure. These data transfer metric approximate parity into probability fields for rounding.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific infrastructure in the import closure; individual helper assertions are not represented as separately numbered paper theorems. Original Lean module AbelianTargets/SupportModel.lean, selected declaration lines 16-23, 25-33; SHA-256 a08106238ed36657e7cbfa18beceaf4b4c73df65936692a02ac81f08b9a4283c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

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

/-- The assertion of Proposition 6.1, expressed without committing to a
particular auxiliary compact metric complex. -/
def ApproximateParityMaps {d : ℕ} (X Y : Type*)
    [TopologicalSpace X] [AddAction (Lattice d) X] [MetricSpace Y]
    (τ : Y → Y) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : X → Y,
    Continuous f ∧ (Set.range f).Finite ∧
      ∀ (x : X) (i : Fin d), dist (f (unitVector i +ᵥ x)) (τ (f x)) < ε

/-- Coordinates of the map into `𝒟(H)` used in Lemma 6.2. The first-shore
swap identity is the part of equivariance needed in the rounding argument. -/
structure SupportModel {Y V : Type*} [TopologicalSpace Y] [Fintype V]
    (H : SimpleGraph V) (τ : Y → Y) where
  p : Y → Probability V
  q : Y → Probability V
  continuous_p : Continuous p
  compatible : ∀ y, Compatible H (p y) (q y)
  first_swap : ∀ y, p (τ y) = q y





end AbelianTargets


