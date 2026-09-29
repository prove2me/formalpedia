-- Prove2me | Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
-- name    : mme_dwz_table2_compatible_outer_candidate_prime_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T20:17:04.800638+00:00
-- url     : https://prove2.me/theorems/d5a5b3e1-d839-4720-8530-fa192883f4a7
-- title:
--   DWZ Claim 6.8: finite prime budget for Table-2 compatible candidates
-- statement:
--   For every integral Table-2 multiplier m, construct a concrete fixed coarse Z-word K, its nonempty family of all exact matchable outer component words, and its nonempty exact typical fine fiber. For every retained outer word and every typical fine word, let the candidate set consist exactly of the other compatible outer words. Its cardinal is at most the explicit degree-nine finite compatibility-rate bound R. Moreover, there is an odd prime p with 4 < p, eight times the candidate cardinal at most p, and max(4,8|C|) < p ≤ 2 max(4,8|C|). In particular, after casting to the reals, p ≤ max(8,16R). The statement includes m=0 and an empty candidate set, and deliberately makes no claim about the separate first-collision budget.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.6, Lemma 6.7, Equations (21)--(23), and Claim 6.8, printed pp. 54--57 (PDF pp. 55--58); https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_count_upper
import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus
import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_compatible_outer_candidate_prime_budget (m : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let regionOfShape :
          Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
        if h : MME.DWZSquare.shapeX s = 0 ∨
            MME.DWZSquare.shapeY s = 0 then
          Sum.inl ⟨s, h⟩
        else
          Sum.inr (MME.DWZSquare.shapeZ s)
      let Outer :=
        {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t // w t = s} =
            MME.DWZTable2Counts.component s * m}
      let Typical :=
        {small : Fin (MME.DWZTable2Counts.scale * m) → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ p, Fintype.card {t // small t = p} =
            MME.DWZTable2Counts.gamma p * m}
      let Compatible : Outer → Typical → Prop := fun I small ↦
        ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
          Fintype.card
              {t //
                regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
            MME.DWZTable2Cardinality.cellCount m r a
      let R : ℝ :=
        (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      (∀ k, Fintype.card {t // K t = k} =
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
        ∀ (retained : Outer) (small₀ : Typical),
          ∃ candidates : Finset Outer,
            (∀ I, I ∈ candidates ↔
              I ≠ retained ∧ Compatible I small₀) ∧
            (candidates.card : ℝ) ≤ R ∧
              ∃ p : ℕ,
                p.Prime ∧ Odd p ∧
                4 < p ∧
                8 * candidates.card ≤ p ∧
                max 4 (8 * candidates.card) < p ∧
                p ≤ 2 * max 4 (8 * candidates.card) ∧
                (p : ℝ) ≤ max 8 (16 * R) := by
  sorry
