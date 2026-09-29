-- Prove2me | Theorems.Thm_mme_dwz_table2_equation21_combined_prime_budget
-- name    : mme_dwz_table2_equation21_combined_prime_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T21:17:27.2854+00:00
-- url     : https://prove2.me/theorems/f3b91242-0268-4aca-82c9-ceb97fa78122
-- title:
--   DWZ Equation (21): one Table-2 prime for both collision budgets
-- statement:
--   For every integral Table-2 multiplier m, retain the exact global full-marginal X/Y star degree d, its nonempty block and triple families, both uniform-star identities, both division-free incidence factorizations, and the exact X/Y multinomial counts. Also construct the concrete fixed coarse Z-word K, nonempty outer and typical families, and the exact compatible competitor set for every retained outer word and typical fine word, preserving its explicit finite real rate bound R. For each such pair set M0 = max(4, 8 max(d, |C|)). Then one odd prime p simultaneously satisfies 4 < p, 8d ≤ p, 8|C| ≤ p, and M0 < p ≤ 2M0. This is the finite combined modulus-selection step of DWZ Equation (21); it makes no retention-probability, asymptotic bound on d, or final survival claim.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, Section 6.2 Equation (21), and Claim 6.8; https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
import Theorems.Thm_mme_dwz_table2_compatible_outer_candidate_prime_budget
import Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_equation21_combined_prime_budget (m : ℕ) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    let YWord :=
      {J : Fin sourceLength → Fin 5 //
        ∀ y, Fintype.card {t // J t = y} = alphaY y}
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    let xWord : MarginalTriple → XWord := fun w ↦
      ⟨fun t ↦ MME.DWZSquare.shapeX (w.1 t), w.2.1⟩
    let yWord : MarginalTriple → YWord := fun w ↦
      ⟨fun t ↦ MME.DWZSquare.shapeY (w.1 t), w.2.2.1⟩
    let FixedX : XWord → Type := fun I ↦
      {w : MarginalTriple // xWord w = I}
    let FixedY : YWord → Type := fun J ↦
      {w : MarginalTriple // yWord w = J}
    ∃ d : ℕ,
      Nonempty XWord ∧
      Nonempty YWord ∧
      Nonempty MarginalTriple ∧
      0 < d ∧
      (∀ I : XWord, Nat.card (FixedX I) = d) ∧
      (∀ J : YWord, Nat.card (FixedY J) = d) ∧
      Nat.card MarginalTriple = Nat.card XWord * d ∧
      Nat.card MarginalTriple = Nat.card YWord * d ∧
      Nat.card XWord = Nat.multinomial Finset.univ alphaX ∧
      Nat.card YWord = Nat.multinomial Finset.univ alphaY ∧
      Nat.card XWord = Nat.card YWord ∧
      (∀ I : XWord, 4 * Nat.card (FixedX I) ≤ 8 * d) ∧
      (∀ J : YWord, 4 * Nat.card (FixedY J) ≤ 8 * d) ∧
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
              let M0 := max 4 (8 * max d candidates.card)
              ∃ p : ℕ,
                p.Prime ∧ Odd p ∧
                4 < p ∧
                8 * d ≤ p ∧
                8 * candidates.card ≤ p ∧
                M0 < p ∧ p ≤ 2 * M0 := by
  sorry
