-- Prove2me | Theorems.Thm_burau_faithful_three_reduction
-- name    : burau_faithful_three_reduction
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:20:39.203469+00:00
-- url     : https://prove2.me/theorems/619e159a-74a5-4bbe-9d7a-73707add5b57
-- title:
--   The free-group criterion implies faithfulness for B_3
-- statement:
--   **The free-group criterion implies faithfulness of the Burau representation of $B_3$.**
--
--   Let $\rho_3 : B_3 \to \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}])$ be the unreduced Burau representation, and let
--   $\sigma_1,\sigma_2$ be the Artin generators, so that $B_3=\langle \sigma_1,\sigma_2 \mid \sigma_1\sigma_2\sigma_1 = \sigma_2\sigma_1\sigma_2\rangle$.
--   Assume the *free-group criterion*: for every word $w$ in the free group on two generators,
--   $$\rho_3\bigl([w]\bigr)=1 \iff w\in \bigl\langle\!\bigl\langle\,\sigma_1\sigma_2\sigma_1(\sigma_2\sigma_1\sigma_2)^{-1}\,\bigr\rangle\!\bigr\rangle .$$
--   Under this hypothesis $\rho_3$ is injective: an element killed by $\rho_3$ is represented by a word in the
--   normal closure of the defining relator, hence is trivial in $B_3$ by the presentation.
--
--   This isolates the combinatorial input (the criterion, whose easy direction is already proved) from the
--   group-theoretic assembly, and decomposes the milestone target
--   `BurauFaithful.burau_faithful_three` into two provable children.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3 (Theorem 3.15); W. Magnus, A. Peluso, *On a theorem of V. I. Arnold*, Comm. Pure Appl. Math. 22 (1969).

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

theorem burau_faithful_three_reduction
    (hc : ∀ w : FreeGroup (Fin 2),
      BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 ↔
        w ∈ Subgroup.normalClosure (BraidsLinksMCG.braidRels 3)) :
    Function.Injective (BurauFaithful.burauRep 3) := by sorry
