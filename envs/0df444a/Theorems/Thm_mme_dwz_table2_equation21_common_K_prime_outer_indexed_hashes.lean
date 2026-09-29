-- Prove2me | Theorems.Thm_mme_dwz_table2_equation21_common_K_prime_outer_indexed_hashes
-- name    : mme_dwz_table2_equation21_common_K_prime_outer_indexed_hashes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T08:55:36.127182+00:00
-- url     : https://prove2.me/theorems/19b59064-ce8e-49fe-b1d1-1effc128c3a4
-- title:
--   Outer-indexed common witness for both Equation-(21) hash stages
-- statement:
--   For every positive Table-2 scale, one common degree, coarse Z-word, collision maximum, and prime support both asymmetric hashing stages. Every word retained by the fixed-K first hash has a literal Outer representative under inverse reindexing, the target cardinal equals Nat.card Outer exactly, the first-hash rate is stated using that source cardinal, and the same K and p leave at least seven eighths of every useful literal brokenCopy as nonholes.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Equation (21), Lemma 6.7, and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_equation21_common_K_prime_first_and_second_hash
import Theorems.Thm_mme_dwz_table2_fixed_K_reindexed_target_equiv_outer
import Theorems.Thm_mme_dwz_table2_claim6_8_useful_brokenCopy_seven_eighths

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_equation21_common_K_prime_outer_indexed_hashes
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
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∃ d : ℕ, ∃ K : Fin L → Fin 5,
      let Outer :=
        {w : Fin L → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t : Fin L // w t = s} =
            MME.DWZTable2Counts.component s * m}
      let Typical :=
        {small : Fin L → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ q, Fintype.card {t : Fin L // small t = q} =
            MME.DWZTable2Counts.gamma q * m}
      let Compatible : Outer → Typical → Prop := fun I small ↦
        ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
          Fintype.card
              {t : Fin L //
                regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
            MME.DWZTable2Cardinality.cellCount m r a
      let candidates : Outer → Typical → Finset Outer := fun retained small ↦
        Finset.univ.filter
          (fun B : Outer ↦ B ≠ retained ∧ Compatible B small)
      let R : ℝ :=
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      let FixedK : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
        (∀ t, MME.DWZSquare.shapeZ (a t) = K (reindex t)) ∧
        ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
          MME.DWZTable2Counts.component s * m
      let T := A.filter FixedK
      ∃ D p : ℕ, ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
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
        (∀ k, Fintype.card {t : Fin L // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧ Nonempty Typical ∧
        (∀ retained small, (candidates retained small).card ≤ D) ∧
        (D : ℝ) ≤ R ∧
        Odd p ∧ 4 < p ∧ 8 * d ≤ p ∧
        (∀ retained small,
          8 * (candidates retained small).card ≤ p) ∧
        max 4 (8 * max d D) < p ∧
        p ≤ 2 * max 4 (8 * max d D) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
        (∀ a ∈ T, ∃ w : Outer,
          w.1 = fun t ↦ a (reindex.symm t)) ∧
        T.card = Nat.card Outer ∧
          (∀ (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
            (hSfree : ThreeAPFree (S : Set ℕ)),
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
              ((Nat.card Outer : ℝ) * (S.card : ℝ)) /
                  (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ)) ∧
        ∀ (retained : Outer) (b0 : ZMod p),
          let Block := MME.DWZTable2StandardForm.UsefulBlock m retained.1
          let addressX : Outer → Fin (N + 1) → Fin 5 := fun I t ↦
            MME.DWZSquare.shapeX (I.1 (reindex t))
          let addressZ : Fin (N + 1) → Fin 5 := fun t ↦ K (reindex t)
          let hX : (Fin (N + 1) → ZMod p) →
              (Fin (N + 1) → Fin 5) → ZMod p := fun w X ↦
            b0 + ∑ t, ((X t).val : ZMod p) * w t
          let hZ : ZMod p → (Fin (N + 1) → ZMod p) →
              (Fin (N + 1) → Fin 5) → ZMod p := fun w0 w Z ↦
            b0 + (2 : ZMod p)⁻¹ *
              (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)
          let conditionedW0 : (Fin (N + 1) → ZMod p) → ZMod p :=
            fun w ↦
              2 * (∑ t, ((addressX retained t).val : ZMod p) * w t) -
                ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
          let hashRetained :
              Outer → (Fin (N + 1) → ZMod p) → Prop := fun B w ↦
            hX w (addressX B) = hZ (conditionedW0 w) w addressZ
          ∃ smallOf : Block → Typical,
            (∀ z : Block,
              (smallOf z).1 = z.1 ∧ Compatible retained (smallOf z)) ∧
            ∃ w : Fin (N + 1) → ZMod p,
              7 * Fintype.card Block ≤
                8 * (MME.DWZStep2.brokenCopy
                  (fun z B ↦
                    Compatible B (smallOf z) ∧ hashRetained B w)
                  (fun _ _ ↦ True) retained).nonholes.card := by
  sorry
