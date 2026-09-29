-- Prove2me | Theorems.Thm_mme_dwz_table2_integer_counts_exact
-- name    : mme_dwz_table2_integer_counts_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:57:24.496853+00:00
-- url     : https://prove2.me/theorems/dc037102-eaea-4cd4-aff9-76662570556b
-- title:
--   DWZ Table 2: exact integral realization of all probability data
-- statement:
--   Let S = 10^16. Interpret the fifteen component weights alpha, their three-way Z splits, the typical-pair distribution gamma, the Z marginal alpha_Z, and the interior (+,+,k) split distributions from DWZ Table 2 as exact terminating decimals. The stated natural-valued tables are exactly S times the corresponding probabilities (or, for an interior split, S times its mass times its conditional split probability). Every component row sums to its component count, both gamma and alpha_Z have total S, and every interior split row sums to its interior mass. Thus all Table 2 inputs to the multinomial quotient in Equation (23) have one common exact integral realization. This supplies the arithmetic bridge from the printed rational certificate to the finite counting and entropy theorems; it asserts no numerical omega bound by itself.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.4, Lemma 6.7, Equation (23), Section 6.3 and Table 2 (printed pp. 54-59 / PDF pp. 55-60).

import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts

open BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_integer_counts_exact :
    (∀ s : Fin 15,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.alpha s =
        MME.DWZTable2Counts.component s) ∧
    (∀ s : Fin 15, ∀ r : Fin 3,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.alpha s *
          MME.DWZSquare.zSplit s r =
        MME.DWZTable2Counts.split s r) ∧
    (∀ s : Fin 15,
      ∑ r, MME.DWZTable2Counts.split s r =
        MME.DWZTable2Counts.component s) ∧
    (∑ s, MME.DWZTable2Counts.component s =
      MME.DWZTable2Counts.scale) ∧
    (∑ p, MME.DWZTable2Counts.gamma p =
      MME.DWZTable2Counts.scale) ∧
    (∑ k, MME.DWZTable2Counts.alphaZ k =
      MME.DWZTable2Counts.scale) ∧
    (∀ k : Fin 5,
      ∑ r, MME.DWZTable2Counts.plusSplit k r =
        MME.DWZTable2Counts.plusMass k) ∧
    (∀ p : Fin 3 × Fin 3,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.gamma p =
        MME.DWZTable2Counts.gamma p) ∧
    (∀ k : Fin 5,
      (MME.DWZTable2Counts.scale : ℝ) *
          mme_modern_marginal MME.DWZSquare.shapeZ MME.DWZSquare.alpha k =
        MME.DWZTable2Counts.alphaZ k) ∧
    (∀ k : Fin 5,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.plusMass k =
        MME.DWZTable2Counts.plusMass k) ∧
    ∀ k : Fin 5, ∀ r : Fin 3,
      (MME.DWZTable2Counts.scale : ℝ) * MME.DWZSquare.plusMass k *
          MME.DWZSquare.plusSplit k r =
        MME.DWZTable2Counts.plusSplit k r := by
  sorry
