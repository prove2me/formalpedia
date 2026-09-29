-- Prove2me | Theorems.Thm_image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne
-- name    : image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/fb4f3ba8-1c41-56de-8747-a5b01c0553eb
-- title:
--   Component-swapping homeomorphism moves a connected component off itself
-- statement:
--   Let $X$ be a topological space and let $Z_1, Z_2 \subseteq X$ be closed subsets which are irreducible (nonempty and preirreducible), with $Z_1 \cup Z_2 = X$ and with neither contained in the other. Let $\tau : X \simeq X$ be a homeomorphism such that $\tau(Z) \neq Z$ for every $Z$ in `irreducibleComponents X`, i.e. $\tau$ maps no maximal irreducible subset of $X$ onto itself. Let $U \subseteq X$ be a subset with $\tau(U) = U$, and let $p \in X$ be a point such that the traces of the two pieces on $U$ are the connected component of $p$ in $U$ and its complement in $U$: $Z_1 \cap U =$ `connectedComponentIn U p` and $Z_2 \cap U = U \setminus$ `connectedComponentIn U p`. The conclusion is that for every $y$ in the connected component of $p$ in $U$, the point $\tau y$ lies in $U \setminus$ `connectedComponentIn U p`; equivalently, $\tau$ carries that connected component into its complement inside $U$.
--
--   A purely topological statement about a space covered by two closed irreducible subsets, neither contained in the other, so that these are precisely its irreducible components and any homeomorphism either fixes each of them or interchanges them. It is used in the construction of the regular model of $X_1(Mp)$, where the relevant bad geometric fibre consists of two crossing curves, $U$ is an invariant open subset, and $\tau$ is the base change of the level-$p$ automorphism; it supplies the clause asserting that $\tau$ moves one connected component of $U$ onto the other.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem image_connectedComponentIn_subset_diff_of_forall_mem_irreducibleComponents_image_ne
    {X : Type u} [TopologicalSpace X] (Z₁ Z₂ : Set X)
    (hZ₁c : IsClosed Z₁) (hZ₂c : IsClosed Z₂) (hZ₁ : IsIrreducible Z₁) (hZ₂ : IsIrreducible Z₂)
    (hcov : Z₁ ∪ Z₂ = Set.univ) (h₁₂ : ¬ Z₁ ⊆ Z₂) (h₂₁ : ¬ Z₂ ⊆ Z₁)
    (τ : X ≃ₜ X) (hτ : ∀ Z ∈ irreducibleComponents X, τ '' Z ≠ Z)
    (U : Set X) (hτU : τ '' U = U) (p : X)
    (hU₁ : Z₁ ∩ U = connectedComponentIn U p) (hU₂ : Z₂ ∩ U = U \ connectedComponentIn U p) :
    ∀ y ∈ connectedComponentIn U p, τ y ∈ U \ connectedComponentIn U p := by sorry
