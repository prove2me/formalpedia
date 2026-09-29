-- Prove2me | Theorems.Thm_mme_stothers_fixed_target_pruning_assembly
-- name    : mme_stothers_fixed_target_pruning_assembly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T18:47:35.606127+00:00
-- url     : https://prove2.me/theorems/b01ec191-50f5-4480-87f3-0730acf24dca
-- title:
--   Deterministic target-isolation step for the fixed Davie–Stothers profile
-- statement:
--   Let E be a finite, vertex-closed family of marginal-supported outer addresses at repetition scale m. Then there is a family G of exact-profile addresses that is mode-disjoint and induced, and whose size satisfies
--
--   $$
--   |E_{target}| <= |G| + |C(E)|,
--   $$
--
--   where E_target is the exact Table-1 subfamily and C(E) is the explicitly defined set of ordered target–ambient collisions sharing a mode word.
--
--   This theorem is the deterministic deletion half of the type-1 outer laser. It reuses Prove2Me theorem mme_tripartite_target_isolation_pruning; the remaining analytic-combinatorial task is only to construct E with many target edges and few collisions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proceedings of the Royal Society of Edinburgh A 143 (2013), Section 3, especially Lemma 3.3 and Equation (3.4), pp. 361–363, specialized in Section 5, Theorem 5.3, pp. 366–368. https://doi.org/10.1017/S0308210511001648

import Definitions.Def_mme_stothers_fixed_outer_profile

open MME
open MME.StothersFourth

set_option autoImplicit false

theorem mme_stothers_fixed_target_pruning_assembly
    (m : ℕ) (E : Finset (FixedMarginalSupportedAddress m))
    (hclosed : FixedMarginalVertexClosed E) :
    ∃ G : Finset (FixedExactOuterAddress m),
      FixedInducedModeDisjoint G ∧
      ((fixedExactTargetEdges E).card : ℝ) ≤
        (G.card : ℝ) + (fixedTargetAmbientCollisions E).card := by sorry
