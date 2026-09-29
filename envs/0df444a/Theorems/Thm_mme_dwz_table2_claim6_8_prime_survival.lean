-- Prove2me | Theorems.Thm_mme_dwz_table2_claim6_8_prime_survival
-- name    : mme_dwz_table2_claim6_8_prime_survival
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:33:29.584202+00:00
-- url     : https://prove2.me/theorems/968047b7-9988-42a6-8e40-78601c172fc1
-- title:
--   DWZ Table 2 Claim 6.8: rate-controlled prime gives one-eighth candidate survival
-- statement:
--   Let $m>0$ be an integral multiplier of the exact Table-2 distribution. There is a coarse $Z$-word $K$ with the prescribed marginal histogram, a nonempty family of exact matchable outer component words over $K$, and a nonempty exact typical fine fiber. Fix a retained outer word and a typical fine word, and let $\mathcal C$ be exactly the other compatible outer words. If $R$ is the explicit degree-nine finite compatibility-rate bound, then there is an odd prime $p>4$ such that
--
--   $$
--   |\mathcal C|\le R,\qquad 8|\mathcal C|\le p,\qquad
--   p\le 2\max(4,8|\mathcal C|),\qquad
--   p\le \max(8,16R)
--   $$
--
--   (the last inequality being over the reals). Reindex the positive source word as $\operatorname{Fin}(n+1)$ and condition the DWZ affine hash on the retained $X/Z$ equality. For every decidable bad event, if each bad weight vector has a witness in $\mathcal C$ whose bounded $X$ address collides with the conditioned retained $Z$ hash, then
--
--   $$
--   8|\{w:w\text{ is bad}\}|\le |\operatorname{ZMod}(p)^{n+1}|.
--   $$
--
--   Thus the compatible-candidate prime budget yields the finite one-eighth conclusion once the source-specific hole-to-collision coverage premise is supplied. The prime is chosen separately for each retained/typical pair and does not cover DWZ's separate first-collision budget.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.6, Lemma 6.7, Equations (21)-(23), and Claim 6.8 (printed pp. 54-57, PDF pp. 55-58), together with Table 2 (printed p. 59, PDF p. 60); https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_table2_claim6_8_bounded_address_adapter

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_claim6_8_prime_survival
    (m : ℕ) (hm : 0 < m) :
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
      let R : ℝ :=
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
        MME.DWZSquare.shapeX (I.1 (reindex t))
      let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
      (∀ k, Fintype.card {t : Fin sourceLength // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧
        Nonempty Typical ∧
        Function.Injective
          (fun I : Outer ↦ fun t ↦ MME.DWZSquare.shapeX (I.1 t)) ∧
        Nat.multinomial Finset.univ
            (fun s : Fin 15 ↦ MME.DWZTable2Counts.component s * m) =
          Nat.multinomial Finset.univ
              (fun k : Fin 5 ↦ MME.DWZTable2Counts.alphaZ k * m) *
            Nat.card Outer ∧
        ∀ (retained : Outer) (small : Typical),
          let outerCandidates :=
            Finset.univ.filter
              (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
          ∃ p : ℕ, ∃ hp : p.Prime,
            letI : Fact p.Prime := ⟨hp⟩
            Odd p ∧
              4 < p ∧
              (outerCandidates.card : ℝ) ≤ R ∧
              8 * outerCandidates.card ≤ p ∧
              max 4 (8 * outerCandidates.card) < p ∧
              p ≤ 2 * max 4 (8 * outerCandidates.card) ∧
              (p : ℝ) ≤ max 8 (16 * R) ∧
              ∀ (b0 : ZMod p)
                (bad : (Fin (n + 1) → ZMod p) → Prop)
                [DecidablePred bad],
                let hX : (Fin (n + 1) → ZMod p) →
                    (Fin (n + 1) → Fin 5) → ZMod p :=
                  fun w A ↦ b0 + ∑ t, ((A t).val : ZMod p) * w t
                let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
                    (Fin (n + 1) → Fin 5) → ZMod p :=
                  fun w0 w C ↦
                    b0 + (2 : ZMod p)⁻¹ *
                      (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
                let conditionedW0 :
                    (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
                  2 * (∑ t,
                    ((addressX retained t).val : ZMod p) * w t) -
                    ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
                (∀ w, bad w →
                  ∃ A ∈ outerCandidates,
                    hX w (addressX A) =
                      hZ (conditionedW0 w) w addressZ) →
                8 * (Finset.univ.filter bad).card ≤
                  Fintype.card (Fin (n + 1) → ZMod p) := by
  sorry
