-- Prove2me | Theorems.Thm_mme_stothers_general_target_pruning_assembly
-- name    : mme_stothers_general_target_pruning_assembly
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T05:48:35.311933+00:00
-- url     : https://prove2.me/theorems/2539d63e-d768-432e-b058-f24828458701
-- title:
--   Pruning to an induced mode-disjoint family at any profile
-- statement:
--   **Deterministic pruning of an ambient family to an induced, mode-disjoint subfamily.**
--
--   Fix an integral ten-class profile $\beta$ and a scale $m$, and let $E$ be a vertex-closed family of
--   marginal-supported addresses -- closed in the sense that every supported mixed address assembled
--   from three members of $E$ is again realized in $E$. Then there is a family $G$ of exact-profile
--   addresses that is both *mode-disjoint* (distinct members share no mode word) and *induced* (a
--   supported mixed address built from three members forces those three to coincide), with
--
--   $$\#\{\text{exact-profile targets in } E\} \;\le\; \#G \;+\; \#\{\text{target--ambient collisions in } E\}.$$
--
--   In other words, every target either survives into the pruned family or is accounted for by a
--   collision: deleting one endpoint of each collision leaves an induced matching, and the count lost
--   is at most the number of collisions. This is the deterministic step that converts the probabilistic
--   hash budget -- targets outnumber collisions -- into an actual induced mode-disjoint family, which
--   is what the tensor-side extraction consumes. Vertex closure is what makes the argument
--   deterministic: it guarantees that a supported mixed address of retained vertices is itself a
--   retained edge, so inducedness can be certified inside the family.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Mathlib.Data.Finset.Prod

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_target_pruning_assembly
    (base : Fin 10 → ℕ) (m : ℕ) (E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m))
    (hclosed : MME.StothersFourth.GenMarginalVertexClosed E) :
    ∃ G : Finset (MME.StothersFourth.GenExactOuterAddress base m),
      MME.StothersFourth.GenInducedModeDisjoint G ∧
      ((MME.StothersFourth.genExactTargetEdges E).card : ℝ) ≤
        (G.card : ℝ) + (MME.StothersFourth.genTargetAmbientCollisions E).card := by
  sorry
