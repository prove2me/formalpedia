-- Prove2me | Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree_rate
-- name    : mme_dwz_table2_first_hash_uniform_xy_degree_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:28:54.729182+00:00
-- url     : https://prove2.me/theorems/1b29e12a-c2a0-443d-a1d3-bcb2611257b0
-- title:
--   Entropy-rate upper bound for the exact Table-2 first-hash degree
-- statement:
--   For every nonnegative Table-2 scale multiplier m, there is one positive natural degree d that is exactly the common size of every fixed-X and fixed-Y star in the family with all three prescribed marginals. The theorem preserves the exact division-free factorization identities and exact X/Y multinomial counts. In addition, d is at most the explicit polynomial loss (6(n+1))^5 (n+1)^15 times exp(m scale log(2) (H_max - H(alpha_X))). The zero-scale case is included.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, first branch of Equation (21), Section 3.10, Equation (25), Algorithm 2, and Table 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_dwz_multinomial_entropy_upper
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_dwz_table2_entropy_potential
import Theorems.Thm_mme_modern_entropyBits_additive_certificate

open scoped BigOperators

set_option autoImplicit false

/-!
# Entropy-rate bound for the first Table-2 hashing degree

This is the analytic continuation of
`mme_dwz_table2_first_hash_uniform_xy_degree`.  The same natural number `d`
is the exact common X- and Y-star degree in the full family with all three
prescribed marginals.  Here it is bounded at the first branch of the
Equation-(21) rate, with every finite loss displayed.
-/

theorem mme_dwz_table2_first_hash_uniform_xy_degree_rate (m : ℕ) :
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
      (d : ℝ) ≤
        (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 5 *
          (((sourceLength + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) := by
  sorry
