-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_exact_profile_subset_marginal_family
-- name    : mme_dwz_table2_reindexed_exact_profile_subset_marginal_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T01:36:17.353908+00:00
-- url     : https://prove2.me/theorems/d07c56c2-18f4-4a29-924c-13417ffd086e
-- title:
--   The exact Table-2 profile family lies in the global marginal family
-- statement:
--   Let $T$ be the finite family of words whose multiplicity in every one of the fifteen DWZ Table-2 cells is exactly $m c_s$. Let $A$ be any family characterized by the corresponding prescribed coarse $X$, $Y$, and $Z$ histograms. Then
--
--   $$
--   T\subseteq A.
--   $$
--
--   The result is the exact interface needed to run the global first hash on the marginal family while retaining only words with the sharper fifteen-cell joint profile. It is valid for every source length $N+1$; if the prescribed profile is impossible at that length, the source family is empty and the inclusion remains exact.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 (printed p. 59; PDF p. 60) and the source-word marginal families in Sections 5–6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_exact_profile_XYZ_marginals

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_reindexed_exact_profile_subset_marginal_family
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
  sorry
