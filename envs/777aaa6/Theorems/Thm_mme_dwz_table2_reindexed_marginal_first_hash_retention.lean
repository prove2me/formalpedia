-- Prove2me | Theorems.Thm_mme_dwz_table2_reindexed_marginal_first_hash_retention
-- name    : mme_dwz_table2_reindexed_marginal_first_hash_retention
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:18:53.078651+00:00
-- url     : https://prove2.me/theorems/fe621176-6b37-4327-9f24-7dcbeee05500
-- title:
--   Reindexed Table-2 marginal family with affine-hash retention
-- statement:
--   For every positive Table-2 multiplicity m, reindex the raw prescribed-marginal word family from its natural length L to the affine-hash convention N+1=L. The resulting finite family has the same cardinality, one exact positive X/Y star degree d, and the published explicit Equation-(21) degree-rate bound. For every odd prime modulus p with 5 ≤ p and 4d ≤ p, and every three-term-progression-free set S in the lower half of Z/pZ, one affine state retains an X/Y-induced subfamily I satisfying |I| ≥ |A||S|/(2p²).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Equation (21), and Table 2.

import Theorems.Thm_mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
import Theorems.Thm_mme_dwz_table2_raw_marginal_family_uniform_xy_degree

open scoped BigOperators
set_option autoImplicit false

theorem mme_dwz_table2_reindexed_marginal_first_hash_retention
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
        ∃ E : ((Fin (N + 2) → ZMod p) × ZMod p) →
            Finset (Fin (N + 1) → Fin 15),
          (∀ q, E q ⊆ A) ∧
          ∃ q, ∃ I : Finset (Fin (N + 1) → Fin 15),
            I ⊆ A ∧ I ⊆ E q ∧
            (∀ e ∈ I, ∀ e' ∈ E q,
              (fun t ↦ MME.DWZSquare.shapeX (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeX (e' t)) ∨
                (fun t ↦ MME.DWZSquare.shapeY (e t)) =
                  (fun t ↦ MME.DWZSquare.shapeY (e' t)) → e = e') ∧
            ((A.card : ℝ) * (S.card : ℝ)) /
                (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)) := by
  sorry
