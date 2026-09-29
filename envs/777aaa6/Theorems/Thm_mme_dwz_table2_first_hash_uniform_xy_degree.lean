-- Prove2me | Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
-- name    : mme_dwz_table2_first_hash_uniform_xy_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T21:01:11.782144+00:00
-- url     : https://prove2.me/theorems/c2c43d98-b084-465e-afc5-20a40cee7416
-- title:
--   DWZ Table 2: exact uniform X/Y degree for the first asymmetric hash
-- statement:
--   Fix an integral multiplier $m$ for the exact Table 2 distribution, and consider all length-$10^{16}m$ words in the fifteen supported level-two component shapes whose induced $X$-, $Y$-, and $Z$-histograms equal the prescribed Table 2 marginals. Let $N_{\mathrm{marg}}$ be the number of these marginal-supported triples, and let $N_{BX}$ and $N_{BY}$ be the numbers of admissible $X$- and $Y$-words.
--
--   There is a positive integer $d$ such that every fixed-$X$ star and every fixed-$Y$ star contains exactly $d$ marginal-supported triples, and
--
--   $$
--   N_{\mathrm{marg}}=N_{BX}d=N_{BY}d.
--   $$
--
--   Moreover, $N_{BX}$ and $N_{BY}$ are the exact multinomial counts of their prescribed histograms and are equal. Consequently the Section 3.10 collision requirement $4d$ is dominated by the Section 6.2 scale $8d$ in both modes.
--
--   This is the division-free finite realization of $N_{\alpha_X,\alpha_Y,\alpha_Z}/N_{BX}$, the first argument in Equation (21)'s modulus scale. It does not choose a prime, perform the random hash, or include the separate compatible-fine-$Z$ budget used in Claim 6.8.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173v5, Section 3.10 (printed pp. 24–26) and Section 6.2, Equation (21) (printed pp. 53–54).

import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_first_hash_uniform_xy_degree (m : ℕ) :
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
      ∀ J : YWord, 4 * Nat.card (FixedY J) ≤ 8 * d := by
  sorry
