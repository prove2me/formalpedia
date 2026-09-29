-- Prove2me | Theorems.Thm_mme_dwz_central_022_202_restricted_source_words_restrict
-- name    : mme_dwz_central_022_202_restricted_source_words_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:52:43.744508+00:00
-- url     : https://prove2.me/theorems/94372d70-2372-434e-874a-e76b8c437fe3
-- title:
--   Source-faithful prescribed-word restrictions of the central 022 and 202 powers
-- statement:
--   Let \(\mathcal W\) be the family of prescribed central-channel words and set \(D=|\mathcal W|\). There are explicit modewise linear maps restricting the \(m\)-fold powers of the canonical 022 and 202 CW-square blocks to\n\n$$\n\langle 1,1,D\rangle \quad\text{and}\quad \langle D,1,1\rangle,\n$$\n\nrespectively. These maps send the complete source tensors to the displayed matrix-multiplication tensors. Moreover, every named canonical CW source word is sent to the standard basis triple indexed by that same word under the public enumeration of \(\mathcal W\).\n\nThis strengthens a dimension-only restriction: the surviving target coordinates are proved to be the literal prescribed source words after one-letter routing, power flattening, and coordinate projection.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Appendix A, https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_central_restricted_word_projectors

open PiTensorProduct
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_dwz_central_022_202_restricted_source_words_restrict
    (K : Type u) [Field K] (q m L G : ℕ) :
    (exists maps022 : ∀ s : Fin 3,
        ((Central022Block K q).kronPow m).V s →ₗ[K]
          (MMObj K 1 1
            (Nat.card (CentralRestricted022Word q m L G))).V s,
      PiTensorProduct.map maps022 ((Central022Block K q).kronPow m).t =
          (MMObj K 1 1
            (Nat.card (CentralRestricted022Word q m L G))).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps022 s
            (central022SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          restricted022TargetMMVec K
            (Nat.card (CentralRestricted022Word q m L G))
            (centralRestrictedWordEquivFin q m L G w) s) ∧
    (exists maps202 : ∀ s : Fin 3,
        ((Central202Block K q).kronPow m).V s →ₗ[K]
          (MMObj K
            (Nat.card (CentralRestricted022Word q m L G)) 1 1).V s,
      PiTensorProduct.map maps202 ((Central202Block K q).kronPow m).t =
          (MMObj K
            (Nat.card (CentralRestricted022Word q m L G)) 1 1).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps202 s
            (central202SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          restricted202TargetMMVec K
            (Nat.card (CentralRestricted022Word q m L G))
            (centralRestrictedWordEquivFin q m L G w) s) := by
  sorry
