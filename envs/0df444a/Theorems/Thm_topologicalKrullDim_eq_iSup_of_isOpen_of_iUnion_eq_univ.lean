-- Prove2me | Theorems.Thm_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ
-- name    : topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/e1c50123-140b-5735-9074-a82872a91c9e
-- title:
--   Topological Krull dimension is local on an open cover
-- statement:
--   Let $T$ be a topological space (in `Type`) and let $\iota$ be an index type. Given a family $W : \iota \to \mathrm{Set}\,T$ such that each $W_i$ is open, and such that $\bigcup_i W_i = T$ (equality of sets with `Set.univ`), the theorem asserts the equality
--   $$\operatorname{topologicalKrullDim} T \;=\; \bigsqcup_i \operatorname{topologicalKrullDim} W_i,$$
--   where each $W_i$ carries the subspace topology via its coercion to a type, and $\operatorname{topologicalKrullDim}$ is the Krull dimension of the poset of irreducible closed subsets, taking values in `WithBot ℕ∞`; the supremum is the indexed supremum in that complete lattice. In particular, since the value $\bot$ is used for a space with no irreducible closed subsets, the convention is built in that the empty space and an empty supremum both give $\bot$: if $\iota$ is empty the covering hypothesis forces $T$ to be empty, and both sides equal $\bot$. No separation, quasi-compactness or non-degeneracy hypotheses are imposed, and the index type is arbitrary.
--
--   This is the statement that topological dimension is local on a space: the dimension of a space equals the supremum of the dimensions of the members of any open cover. It is used in the project to show that the locus where the fibre dimension of a smooth proper morphism takes a given value is clopen.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem topologicalKrullDim_eq_iSup_of_isOpen_of_iUnion_eq_univ
    {T : Type} [TopologicalSpace T] {ι : Type} (W : ι → Set T) (hW : ∀ i, IsOpen (W i))
    (hcov : ⋃ i, W i = Set.univ) :
    topologicalKrullDim T = ⨆ i, topologicalKrullDim ↥(W i) := by sorry
