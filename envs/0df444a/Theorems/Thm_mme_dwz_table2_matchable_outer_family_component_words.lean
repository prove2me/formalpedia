-- Prove2me | Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
-- name    : mme_dwz_table2_matchable_outer_family_component_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T18:37:03.205064+00:00
-- url     : https://prove2.me/theorems/e3f83668-82a1-45a6-9f5d-da2fc74aea05
-- title:
--   DWZ Table 2: fixed-$Z$ family of matchable component words
-- statement:
--   Fix a natural multiplier $m$. For the exact fifteen component types in Duan--Wu--Zhou Table 2, there exists a coarse $Z$-word $K$ of length $10^{16}m$ with the prescribed five-entry marginal histogram. Let $\mathcal O_K$ be the family of all fifteen-valued component words whose $Z$-coordinate agrees pointwise with $K$ and whose component histogram is the exact Table-2 histogram multiplied by $m$. Then $\mathcal O_K$ is nonempty, every member has the required component histogram and fixed $Z$-word, and two members with the same projected $X$-word are equal. Its cardinality is the product of the five local multinomial coefficients obtained by fixing each $Z$-coordinate. Moreover, the global count satisfies the exact division-free identity
--
--   $$
--   N_\alpha=N_{B_Z}\,|\mathcal O_K|.
--   $$
--
--   Here $N_\alpha$ is the multinomial coefficient of the fifteen joint component counts and $N_{B_Z}$ is the multinomial coefficient of the five $Z$-marginal counts. This is the literal fixed-$K$ family averaged over in Equation (22) and the $N_\alpha/N_{B_Z}$ candidate count used in Claim 6.8. It supplies the source-specific outer family needed before the compatibility and hashing arguments.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Definition 6.6, Equation (22), Lemma 6.7 and Claim 6.8 (printed pp. 54-57, PDF pp. 55-58), specialized to Section 6.3, Table 2 (printed pp. 58-59); https://arxiv.org/abs/2210.10173.

import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_table2_integer_counts_exact

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_matchable_outer_family_component_words (m : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let Outer :=
        {w : Fin (MME.DWZTable2Counts.scale * m) → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t // w t = s} =
            MME.DWZTable2Counts.component s * m}
      (∀ k, Fintype.card {t // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧
        (∀ (I : Outer) (s : Fin 15),
          Fintype.card {t // I.1 t = s} =
            MME.DWZTable2Counts.component s * m) ∧
        (∀ (I : Outer) (t),
          MME.DWZSquare.shapeZ (I.1 t) = K t) ∧
        Function.Injective
          (fun I : Outer => fun t => MME.DWZSquare.shapeX (I.1 t)) ∧
        Nat.card Outer =
          ∏ k : Fin 5, Nat.multinomial Finset.univ
            (fun s : {s : Fin 15 // MME.DWZSquare.shapeZ s = k} =>
              MME.DWZTable2Counts.component s.1 * m) ∧
        Nat.multinomial Finset.univ
            (fun s : Fin 15 => MME.DWZTable2Counts.component s * m) =
          Nat.multinomial Finset.univ
              (fun k : Fin 5 => MME.DWZTable2Counts.alphaZ k * m) *
            Nat.card Outer := by sorry
