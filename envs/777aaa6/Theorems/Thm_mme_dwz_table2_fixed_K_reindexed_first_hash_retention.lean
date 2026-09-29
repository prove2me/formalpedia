-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_first_hash_retention
-- name    : mme_dwz_table2_fixed_K_reindexed_first_hash_retention
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:04:49.887719+00:00
-- url     : https://prove2.me/theorems/519b3986-b074-438c-82ad-b80fdbc36197
-- title:
--   First-hash retention on a fixed Table-2 coarse-Z fiber
-- statement:
--   Let A be the finite family of Table-2 component words with the prescribed three marginals, reindexed to the affine-hash coordinate convention. There is one positive uniform X/Y star degree d, obeying the explicit entropy-rate bound, chosen before the coarse Z-word and modulus. For every coarse word K, let T_K be the subfamily of A with the exact fifteen Table-2 component multiplicities and pointwise Z-address K. For every odd prime p at least 5 with 4d ≤ p and every three-term-progression-free S in the lower half of Z/pZ, the first asymmetric hash retains an X/Y-isolated family I inside T_K with |I| ≥ |T_K||S|/(2p²).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Equation (21), Lemma 6.7, and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
import Theorems.Thm_mme_dwz_table2_raw_marginal_family_uniform_xy_degree

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_reindexed_first_hash_retention
    (m : ℕ) (hm : 0 < m) :
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
    let W : (Fin L → Fin 15) ≃ (Fin (N + 1) → Fin 15) :=
      { toFun := fun w t ↦ w (reindex t)
        invFun := fun w t ↦ w (reindex.symm t)
        left_inv := fun w ↦ by funext t; simp
        right_inv := fun w ↦ by funext t; simp }
    let A : Finset (Fin (N + 1) → Fin 15) := A0.map W.toEmbedding
    ∃ d : ℕ,
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
      ∀ (K : Fin L → Fin 5) (p : ℕ) (hp : p.Prime),
        letI : Fact p.Prime := ⟨hp⟩
        ∀ (hpodd : Odd p) (hp5 : 5 ≤ p)
          (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
          (hSfree : ThreeAPFree (S : Set ℕ)),
          let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
            (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
            ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
              MME.DWZTable2Counts.component s * m
          let T := A.filter FixedK
          4 * d ≤ p →
            ∃ E : ((Fin (N + 2) → ZMod p) × ZMod p) →
                Finset (Fin (N + 1) → Fin 15),
              (∀ q, E q ⊆ A) ∧
              ∃ q, ∃ I : Finset (Fin (N + 1) → Fin 15),
                I ⊆ T ∧ I ⊆ E q ∧
                (∀ e ∈ I, ∀ e' ∈ E q,
                  (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                      (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                    (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                      (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
                ((T.card : ℝ) * (S.card : ℝ)) /
                    (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  sorry
