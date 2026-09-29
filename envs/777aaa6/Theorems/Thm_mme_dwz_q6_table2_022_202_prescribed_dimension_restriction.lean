-- Prove2me | Theorems.Thm_mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
-- name    : mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:34:58.45332+00:00
-- url     : https://prove2.me/theorems/385e979e-8efe-46d0-9cda-d06e47a434a9
-- title:
--   DWZ Table-2 022/202: exact prescribed split-word dimension restriction
-- statement:
--   Fix a positive integer t and set m=100000000t, L=3477403t, and G=93045194t. Let D be the number of three-class words of length m with multiplicities L,G,L, together with a pair of six-valued labels at every middle position. The theorem gives genuine matrix-multiplication tensor restrictions of dimensions (1,1,D) and (D,1,1) from the m-fold canonical 022 and 202 constituents of the q=6 Coppersmith--Winograd square. It also proves the exact formula D = binom(m,L) binom(m-L,L) 6^(2G) and unfolds the two corresponding Table-2 componentBase entries to their common normalized scalar formula. This is deliberately a dimension-level result: it does not assert that the restriction witnesses retain the encoded labels, that 022 and 202 share a label-preserving projector, or that these finite dimensions attain the asymptotic component value.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 (printed pp. 58-59 / PDF pp. 59-60) and Appendix A proof of Lemma 4.6(c) (printed pp. 81-82 / PDF pp. 82-83), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_component_022_word_data
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_CW_square_canonical_grading

open MME BigOperators
open MME.DWZSquare
open MME.DWZTable2Component022

universe u

set_option autoImplicit false

theorem mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
    {K : Type u} [Field K] (tau : ℝ) (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let D := Nat.card (Restricted022Word 6 m L G)
    let normalizedBase : ℝ :=
      Real.rpow
        (Real.rpow 6 (2 * ((G : ℝ) / (m : ℝ))) /
          (Real.rpow ((L : ℝ) / (m : ℝ))
              (2 * ((L : ℝ) / (m : ℝ))) *
            Real.rpow ((G : ℝ) / (m : ℝ))
              ((G : ℝ) / (m : ℝ)))) tau
    (TensorObj.Restrict
        (MMObj K 1 1 D)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 0 2 2)).kronPow m) ∧
      TensorObj.Restrict
        (MMObj K D 1 1)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 2 0 2)).kronPow m)) ∧
    D = splitWordCount m L * 6 ^ (2 * G) ∧
    componentBase tau (9 : Fin 15) = normalizedBase ∧
    componentBase tau (10 : Fin 15) = normalizedBase := by sorry
