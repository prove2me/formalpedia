-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one
-- name    : groupCohomology.finiteDimensional_continuous_of_forall_apply_eq_of_rank_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/8ac13949-2609-5c88-8db7-01c964b34659
-- title:
--   Dévissage to trivial lines for continuous H¹ and H²
-- statement:
--   Let $k$ be a field and $G$ a group (both in a fixed universe), let $r \colon G \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ be a group homomorphism into the automorphism group of an algebraic closure of $\mathbb{Q}$, and let $T$ be an object of `Rep k G` which is finite-dimensional over $k$ and on which the action is trivial, i.e. $T.\rho(g)\,t = t$ for all $g \in G$ and $t \in T$. Here, for a representation $M$, [`groupCohomology.continuousH1 r M`](def/GroupCohomology_ContinuousH1.html#L28) is the $k$-submodule of $H^1(G,M)$ obtained as the image of the submodule `levelCocycles₁ r M` of $1$-cocycles under the projection `H1π M`, and [`groupCohomology.continuousH2 r M`](def/GroupCohomology_ContinuousH2.html#L108) is the quotient of `levelCocycles₂ r M` by the submodule of those level $2$-cocycles which are $2$-coboundaries. The conclusion is the conjunction of two implications: first, if for every $L$ in `Rep k G` with trivial $G$-action and $\dim_k L = 1$ the space `continuousH1 r L` is finite-dimensional over $k$, then `continuousH1 r T` is finite-dimensional over $k$; second, the same implication with `continuousH1` replaced throughout by `continuousH2`.
--
--   This is the dévissage step reducing finiteness of the continuous (level-constrained) $H^1$ and $H^2$ of a finite-dimensional representation with trivial $G$-action to the case of trivial lines. It is used in the proofs of [`groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH1_of_isOpen_of_primeLocal) and [`groupCohomology.finiteDimensional_continuousH2_of_isOpen_of_primeLocal`](thm.html#groupCohomology.finiteDimensional_continuousH2_of_isOpen_of_primeLocal), where the one-dimensional case is supplied by finiteness statements for the base field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_continuous_of_forall_apply_eq_of_rank_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.finiteDimensional_continuous_of_forall_apply_eq_of_rank_one {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (T : Rep.{u} k G) [FiniteDimensional k T]
    (hT : ∀ (g : G) (t : T), T.ρ g t = t) :
    ((∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 →
        FiniteDimensional k (groupCohomology.continuousH1 r L)) →
      FiniteDimensional k (groupCohomology.continuousH1 r T)) ∧
    ((∀ L : Rep.{u} k G, (∀ (g : G) (x : L), L.ρ g x = x) → Module.finrank k L = 1 →
        FiniteDimensional k (groupCohomology.continuousH2 r L)) →
      FiniteDimensional k (groupCohomology.continuousH2 r T)) := by sorry
