-- Prove2me | Theorems.Thm_ModNullUniversality_compact_coset_unboundedness
-- name    : ModNullUniversality.compact_coset_unboundedness
-- status  : Proved
-- author  : @username
-- created : 2026-11-09T09:02:59.784343+00:00
-- url     : https://prove2.me/theorems/c7e304ee-20dd-402d-86fa-6d01ada79173
-- title:
--   Section 5 — ordinary unboundedness of the compact coset family
-- statement:
--   There are one compact metrizable abelian group $K$, its normalized Haar probability, and a family $(H_T)_{T\in\mathrm{WF}}$ of subgroups of $K$ such that every subgroup and coset graph is $\Delta^0_3$, every graph is a difference of two $F_\sigma$ sets, and
--
--   $$\forall F\ \exists T\in\mathrm{WF}\quad E_{H_T}^K\not\leq_B F,$$
--
--   where $F$ ranges over all Borel equivalence relations on standard Borel spaces. The group and entire family are fixed before the target. This is the existential form of the compact-family conclusion established in the manuscript's unnumbered Section 5 argument. It concerns the whole group, without discarding a null set.
-- source:
--   Universality modulo null sets in the Borel hierarchy, user-supplied unpublished manuscript dated 9 November 2026; SHA-256 48745c75427f83370292c2e4cf91ec06377e80472252db0182599edcd05e2d97, Section 5, unnumbered compact-family unboundedness argument, lines 361–395; its prior tensor-family input is Wang, arXiv:2611.02531v1, Corollary 6.1 and its proof. https://arxiv.org/abs/2611.02531v1

import Definitions.Def_ModNullCompact20261109

set_option autoImplicit false

theorem ModNullUniversality.compact_coset_unboundedness :
    ∃ K : ModNullUniversality.CompactMetrizableHaarGroup,
      ModNullUniversality.IsAbelian K ∧
      ∃ H : ModNullUniversality.WF → Subgroup K.Carrier,
        ModNullUniversality.LowComplexityFamily K H ∧
        ∀ F : ModNullUniversality.StandardBorelEquivalence,
          ∃ T : ModNullUniversality.WF,
            ¬ ModNullUniversality.BorelReducible
              (ModNullUniversality.CosetRelation K (H T)) F.rel := by sorry
