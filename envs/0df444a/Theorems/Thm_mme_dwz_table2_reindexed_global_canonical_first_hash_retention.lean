-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_global_canonical_first_hash_retention
-- name    : mme_dwz_table2_reindexed_global_canonical_first_hash_retention
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T14:04:45.637792+00:00
-- url     : https://prove2.me/theorems/18489d48-7f0a-4d07-a2eb-0b18ca77fa09
-- title:
--   Global Table-2 first-hash retention in the literal canonical affine bucket
-- statement:
--   For every positive Table-2 scale and every admissible odd prime, reindex the full exact-marginal family of coarse square-tensor words into the hash coordinate convention. There is a common marginal degree d and, whenever 4d is at most the prime, a literal affine bucket E_q containing a retained family I. The retained family is isolated by both its full X word and its full Y word, and satisfies |A||S|/(2p^2) <= |I|. Crucially, A is the full marginal family rather than one fixed coarse-Z fiber, so the coarse-Z multiplicity is already included in the count. The use of the public canonical bucket exposes the hash predicates needed by the subsequent Claim 6.8 source construction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, first hashing and pruning in Sections 5-6; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_reindexed_marginal_first_hash_retention
import Theorems.Thm_mme_dwz_table2_first_hash_retention_in_canonical_bucket

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_reindexed_global_canonical_first_hash_retention
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
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
      (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A0 : Finset (Fin L → Fin 15) := Finset.univ.filter P
    ∃ d : ℕ, ∃ A : Finset (Fin (N + 1) → Fin 15),
      (∀ a, a ∈ A ↔ ∃ w ∈ A0,
        (fun t ↦ w (reindex t)) = a) ∧
      A.card = A0.card ∧
      0 < d ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeX (b t)) =
            (fun t ↦ MME.DWZSquare.shapeX (a t)))).card = d) ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeY (b t)) =
            (fun t ↦ MME.DWZSquare.shapeY (a t)))).card = d) ∧
      (d : ℝ) ≤
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
          (((L + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) ∧
      (4 * d ≤ p →
        ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
          ∃ I : Finset (Fin (N + 1) → Fin 15),
            I ⊆ A ∧
            I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
            (∀ e ∈ I, ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
              (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
            ((A.card : ℝ) * (S.card : ℝ)) /
                (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)) := by sorry
