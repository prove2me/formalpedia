-- Prove2me | Theorems.Thm_burau_three_kernel_word_criterion_easy
-- name    : burau_three_kernel_word_criterion_easy
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T18:51:26.698006+00:00
-- url     : https://prove2.me/theorems/60516db8-74ba-4e19-b268-1683dab22804
-- title:
--   Easy direction of the Burau word criterion for B_3
-- statement:
--   **Easy direction of the three-strand Burau word criterion.**
--
--   Let $\rho_3 : B_3 \to \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}])$ be the unreduced Burau representation,
--   realised on the presented group as $\rho_3 = \texttt{PresentedGroup.toGroup}$ applied to the assignment
--   $\sigma_{i+1}\mapsto$ (the Burau matrix of the $i$-th Artin generator). The Burau matrices satisfy the
--   braid relations (`burauGen_relations`), so the composite
--   $$\mathrm{FreeGroup}\twoheadrightarrow B_3\xrightarrow{\ \rho_3\ }\mathrm{GL}_3$$
--   kills every element of the normal closure of Artin's relations. Hence, for every word $w$ in the free
--   group on the two Artin generators,
--   $$ w\in\bigl\langle\!\bigl\langle \texttt{braidRels}\ 3\bigr\rangle\!\bigr\rangle
--      \ \Longrightarrow\ \rho_3\bigl([w]\bigr)=1 .$$
--   This is one direction of the frontier node `BurauFaithful.burau_three_kernel_word_criterion`; the other
--   direction is the Magnus–Peluso theorem. The milestone target `BurauFaithful.burau_faithful_three`
--   follows from the full criterion in 69 lines (`Solutions/Sol_burau_faithful_three.lean`).
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3; W. Magnus, A. Peluso, *On a theorem of V. I. Arnold*, Comm. Pure Appl. Math. 22 (1969).

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

theorem burau_three_kernel_word_criterion_easy (w : FreeGroup (Fin 2))
    (hw : w ∈ Subgroup.normalClosure (BraidsLinksMCG.braidRels 3)) :
    BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 := by sorry
