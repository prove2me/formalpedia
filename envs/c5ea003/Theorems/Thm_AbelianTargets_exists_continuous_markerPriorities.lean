-- Prove2me | Theorems.Thm_AbelianTargets_exists_continuous_markerPriorities
-- name    : AbelianTargets.exists_continuous_markerPriorities
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:50:39.04599+00:00
-- url     : https://prove2.me/theorems/8022657a-cc9d-4606-80db-75ce3a4a4cf5
-- title:
--   Marker priorities use a number of colors independent of the scales
-- statement:
--   Let $d,S\in\mathbb N$ and $L_i\ge1$ be natural scales. Let $\mathbb Z^d$ act freely and continuously on a $T_1$, second-countable space $X$ with a clopen basis, and let $A$ be an anisotropic clopen marker set at scales $L$: its orbit points are separated by some coordinate difference greater than $L_i$, and every orbit point is within coordinate distances $L_i$ of a marker. On the subspace $A$, join distinct markers $x,y$ when $g\cdot x=y$ for a nonzero displacement satisfying $|g_i|\le SL_i$ for every $i$. There is a continuous proper coloring
--   $$c:A\longrightarrow\{0,\ldots,(2S+1)^d-1\}.$$
--   In particular its number of colors depends on $S,d$ and not on the values of $L_i$.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/MarkerPriorities.lean, lines 113–137; SHA256 eea138a37e4856c5f0023b7a1cde74f87d32c4055a60d716211686d01cc78b31.

import Definitions.Def_AT260939824_Actions
import Definitions.Def_AT260939824_AnisotropicMarkers
import Definitions.Def_AT260939824_ClopenMarkers
import Definitions.Def_AT260939824_Dimension
import Definitions.Def_AT260939824_MarkerExistence
import Definitions.Def_AT260939824_MarkerMap
import Definitions.Def_AT260939824_MarkerPriorities
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
# Continuous marker priorities with a scale-independent color bound

The marker proximity graph is the actual induced finite-displacement
graph. Its finite neighbors are counted by the anisotropic packing bound.
The general continuous finite-coloring theorem supplies the priorities.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
variable {d : ℕ} {L : Fin d → ℕ} {X : Type*}
variable [TopologicalSpace X] [AddAction (Lattice d) X]
variable [ContinuousVAdd (Lattice d) X] [T1Space X] [SecondCountableTopology X]

theorem AbelianTargets.exists_continuous_markerPriorities (M : AnisotropicClopenMarkers d L X)
    (hL : ∀ i,1 ≤ L i) (S : ℕ) (zeroDim : ZeroDimensional X)
    (free : IsFree (G := Lattice d) (X := X)) :
    ∃ c : M.markers → Fin ((2*S+1)^d),Continuous c ∧
      ∀ x y,(markerProximityGraph M S free).Adj x y → c x ≠ c y := by sorry
