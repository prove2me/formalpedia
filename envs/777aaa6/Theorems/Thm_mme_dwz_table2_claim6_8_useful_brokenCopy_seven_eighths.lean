-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_useful_brokenCopy_seven_eighths
-- name    : mme_dwz_table2_claim6_8_useful_brokenCopy_seven_eighths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T07:37:31.495954+00:00
-- url     : https://prove2.me/theorems/2ae9979c-dea7-4815-aad0-fee4b46a2b23
-- title:
--   One common Table-2 prime preserves seven eighths of every useful block
-- statement:
--   For every positive Table-2 multiplier m and first-hash degree d, choose the Table-2 coarse word K and one odd prime p before any retained outer word or useful-block element. The prime simultaneously controls every compatible collision fiber and obeys the explicit entropy-rate bound. For each retained outer word and affine offset, every useful-block word canonically becomes a compatible typical word, and one hash weight makes the literal brokenCopy retain at least seven eighths of the whole UsefulBlock, expressed division-free as 7·|UsefulBlock| ≤ 8·|nonholes|.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Equation (21), Section 3.10, and Claim 6.8.

import Theorems.Thm_mme_dwz_table2_claim6_8_uniform_common_prime
import Theorems.Thm_mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
import Theorems.Thm_mme_dwz_step2_exists_broken_copy_seven_eighths
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_claim6_8_useful_brokenCopy_seven_eighths
    (m : ℕ) (hm : 0 < m) (d : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let sourceLength := MME.DWZTable2Counts.scale * m
      let n := sourceLength - 1
      let reindex : Fin (n + 1) ≃ Fin sourceLength :=
        finCongr (by
          dsimp only [n, sourceLength]
          exact Nat.sub_add_cancel
            (Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
      let regionOfShape :
          Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
        if h : MME.DWZSquare.shapeX s = 0 ∨
            MME.DWZSquare.shapeY s = 0 then
          Sum.inl ⟨s, h⟩
        else
          Sum.inr (MME.DWZSquare.shapeZ s)
      let Outer :=
        {w : Fin sourceLength → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t : Fin sourceLength // w t = s} =
            MME.DWZTable2Counts.component s * m}
      let Typical :=
        {small : Fin sourceLength → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ q, Fintype.card {t : Fin sourceLength // small t = q} =
            MME.DWZTable2Counts.gamma q * m}
      let Compatible : Outer → Typical → Prop := fun I small ↦
        ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
          Fintype.card
              {t : Fin sourceLength //
                regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
            MME.DWZTable2Cardinality.cellCount m r a
      let candidates : Outer → Typical → Finset Outer := fun retained small ↦
        Finset.univ.filter
          (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
      let R : ℝ :=
        (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      (∀ k, Fintype.card {t : Fin sourceLength // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧ Nonempty Typical ∧
        ∃ D p : ℕ, ∃ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          (∀ retained small, (candidates retained small).card ≤ D) ∧
          (D : ℝ) ≤ R ∧
          Odd p ∧ 4 < p ∧ 8 * d ≤ p ∧
          (∀ retained small,
            8 * (candidates retained small).card ≤ p) ∧
          max 4 (8 * max d D) < p ∧
          p ≤ 2 * max 4 (8 * max d D) ∧
          (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
          ∀ (retained : Outer) (b0 : ZMod p),
            let Block :=
              MME.DWZTable2StandardForm.UsefulBlock m retained.1
            let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
              MME.DWZSquare.shapeX (I.1 (reindex t))
            let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
            let hX : (Fin (n + 1) → ZMod p) →
                (Fin (n + 1) → Fin 5) → ZMod p := fun w A ↦
              b0 + ∑ t, ((A t).val : ZMod p) * w t
            let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
                (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w C ↦
              b0 + (2 : ZMod p)⁻¹ *
                (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
            let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
              fun w ↦
                2 * (∑ t,
                  ((addressX retained t).val : ZMod p) * w t) -
                  ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
            let hashRetained :
                Outer → (Fin (n + 1) → ZMod p) → Prop := fun A w ↦
              hX w (addressX A) = hZ (conditionedW0 w) w addressZ
            ∃ smallOf : Block → Typical,
              (∀ z : Block,
          (smallOf z).1 = z.1 ∧ Compatible retained (smallOf z)) ∧
              ∃ w : Fin (n + 1) → ZMod p,
                7 * Fintype.card Block ≤
                  8 * (MME.DWZStep2.brokenCopy
                    (fun z A ↦
                      Compatible A (smallOf z) ∧ hashRetained A w)
                    (fun _ _ ↦ True) retained).nonholes.card := by
  sorry
