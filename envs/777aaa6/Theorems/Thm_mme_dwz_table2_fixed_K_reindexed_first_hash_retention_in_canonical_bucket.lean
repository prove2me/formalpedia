-- Prove2me | Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_first_hash_retention_in_canonical_bucket
-- name    : mme_dwz_table2_fixed_K_reindexed_first_hash_retention_in_canonical_bucket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:23:55.082714+00:00
-- url     : https://prove2.me/theorems/96446fbe-3a76-491c-8ddb-2f6274c08ac3
-- title:
--   Fixed-K first-hash retention preserves the canonical affine bucket
-- statement:
--   For every positive Table-2 scale, the reindexed raw marginal family has a common positive X/Y star degree with the stated entropy-rate bound. For any prescribed coarse Z word K and any suitable odd prime, the fixed-K target family retains a subfamily I of size at least |T||S|/(2p²) inside one literal canonical affine bucket. The family remains X/Y-isolated within that bucket. This strengthens the earlier fixed-K result by preserving the exact bucket state needed by Claim 6.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Algorithm 2 and Additional Zeroing-Out Step 1, PDF pp. 52-54; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_first_hash_retention_in_canonical_bucket
import Theorems.Thm_mme_dwz_table2_raw_marginal_family_uniform_xy_degree

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_fixed_K_reindexed_first_hash_retention_in_canonical_bucket
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
            ∃ q : (Fin (N + 2) → ZMod p) × ZMod p,
              ∃ I : Finset (Fin (N + 1) → Fin 15),
                I ⊆ T ∧ I ⊆ MME.dwzTable2AffineHashBucket S A q ∧
                (∀ e ∈ I,
                  ∀ e' ∈ MME.dwzTable2AffineHashBucket S A q,
                    (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                        (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                      (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                        (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
                ((T.card : ℝ) * (S.card : ℝ)) /
                    (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  sorry
