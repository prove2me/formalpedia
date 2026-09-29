-- Prove2me | solution 1 for mme_dwz_table2_reindexed_exact_profile_subset_marginal_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T01:36:26.229643+00:00
-- url     : https://prove2.me/submissions/b6de246a-5b0d-4940-b919-76e47ad9477c

import Theorems.Thm_mme_dwz_table2_exact_profile_XYZ_marginals

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m N : ℕ)
    (A : Finset (Fin (N + 1) → Fin 15))
    (hA : ∀ a, a ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (a t) = x} =
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
          MME.DWZTable2Counts.component s.1 * m) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (a t) = y} =
        ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
          MME.DWZTable2Counts.component s.1 * m) ∧
      ∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (a t) = z} =
        MME.DWZTable2Counts.alphaZ z * m) :
    (Finset.univ.filter fun a : Fin (N + 1) → Fin 15 ↦
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m) ⊆ A := by
  intro a ha
  have haExact : ∀ s, Fintype.card
      {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m :=
    (Finset.mem_filter.mp ha).2
  exact (hA a).mpr
    (mme_dwz_table2_exact_profile_XYZ_marginals m a haExact)
