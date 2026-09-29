-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_global_marginal_family_characterization
-- name    : mme_dwz_table2_reindexed_global_marginal_family_characterization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T01:25:15.509925+00:00
-- url     : https://prove2.me/theorems/cfd8a05e-0c85-4336-887b-640c8c64dc7f
-- title:
--   Canonical reindexing preserves the global Table-2 marginal family
-- statement:
--   Let $L=m\,\mathrm{scale}$ with $m>0$, put $N=L-1$, and use the canonical equivalence $[N+1]\simeq[L]$. Let $A_0$ be the length-$L$ words with the prescribed coarse $X$, $Y$, and $Z$ histograms, and suppose $A$ is exactly their image after reindexing coordinates. Then
--
--   $$
--   a\in A\quad\Longleftrightarrow\quad a\text{ has the prescribed coarse }X,Y,Z\text{ histograms}.
--   $$
--
--   Thus the image presentation of the global DWZ marginal family may be replaced by its intrinsic fiber-cardinality characterization. The positivity assumption on $m$ guarantees that the canonical equivalence has the stated source length.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 (printed p. 59; PDF p. 60) and the source-word marginal families in Sections 5–6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_exact_profile_coarse_Z_counts

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_reindexed_global_marginal_family_characterization
    (m : ℕ) (hm : 0 < m)
    (A : Finset
      (Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15)) :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card
          {t : Fin L // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin L // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card
          {t : Fin L // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    (∀ a, a ∈ A ↔ ∃ w ∈ A0, (fun t ↦ w (reindex t)) = a) →
    ∀ a, a ∈ A ↔
      (∀ x, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeX (a t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeY (a t) = y} = alphaY y) ∧
      ∀ z, Fintype.card
          {t : Fin (N + 1) // MME.DWZSquare.shapeZ (a t) = z} =
        MME.DWZTable2Counts.alphaZ z * m := by
  sorry
