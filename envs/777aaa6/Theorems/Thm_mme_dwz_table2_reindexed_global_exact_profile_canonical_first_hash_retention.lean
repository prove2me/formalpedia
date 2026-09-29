-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention
-- name    : mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T21:16:47.200902+00:00
-- url     : https://prove2.me/theorems/5ceb5a32-db1c-4ee1-b2c0-177973169cfa
-- title:
--   Canonical first hash retains the exact Table-2 joint-profile family
-- statement:
--   Let A be the reindexed family of Table-2 words with the prescribed X, Y, and Z marginals, and let T be its exact fifteen-component joint-profile subfamily. There is one positive uniform X/Y collision degree d, with the standard entropy upper bound, such that T has exactly the prescribed multinomial cardinality. For every admissible prime p with 4d ≤ p and every three-term-progression-free set S in [0,p/2), one canonical affine hash bucket contains an X/Y-isolated subfamily I ⊆ T satisfying |T||S|/(2p²) ≤ |I|. This is the exact-profile version of the first-hash retention step needed by the DWZ Table-2 source construction.
-- source:
--   Duan--Wu--Zhou, arXiv:2210.10173, the first hashing step around Equation (21), combined with the exact Table-2 joint-profile enumeration.

import Theorems.Thm_mme_dwz_table2_reindexed_marginal_first_hash_retention
import Theorems.Thm_mme_dwz_table2_first_hash_retention_in_canonical_bucket
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_exact_profile_word_card

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_reindexed_global_exact_profile_canonical_first_hash_retention
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
    let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t // a t = s} =
        MME.DWZTable2Counts.component s * m
    ∃ d : ℕ, ∃ A : Finset (Fin (N + 1) → Fin 15),
      (∀ a, a ∈ A ↔ ∃ w ∈ A0,
        (fun t ↦ w (reindex t)) = a) ∧
      A.card = A0.card ∧
      (A.filter ExactProfile).card =
        Nat.multinomial Finset.univ
          (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) ∧
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
            I ⊆ A.filter ExactProfile ∧
            I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
            (∀ e ∈ I, ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
              (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
            (((A.filter ExactProfile).card : ℝ) * (S.card : ℝ)) /
                (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)) := by
  sorry
