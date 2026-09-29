-- Prove2me | Theorems.Thm_mme_dwz_cw_square_central_022_202_restricted_word_power_router
-- name    : mme_dwz_cw_square_central_022_202_restricted_word_power_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:13:14.392961+00:00
-- url     : https://prove2.me/theorems/13ef79a1-e935-4ee1-84b5-9e2303ee8563
-- title:
--   Prescribed-word Kronecker-power routers for the central 022 and 202 CW-square constituents
-- statement:
--   Let T_q be the Coppersmith–Winograd tensor over a field K, and let C_022 and C_202 be the central (0,2,2) and (2,0,2) constituents of its canonically graded square. For integers m,L,G ≥ 0, let W(q,m;L,G) be the prescribed words having L positions in each exceptional channel class and G middle positions, each middle position carrying an ordered label in [q] × [q]. Then there are modewise linear maps with\n\n$$\nC_{022}^{\\otimes m} \\longrightarrow \\langle 1,1,q^2+2\\rangle^{\\otimes m},\\qquad\nC_{202}^{\\otimes m} \\longrightarrow \\langle q^2+2,1,1\\rangle^{\\otimes m},\n$$\n\nwhich send each complete source tensor power to the displayed standard matrix-multiplication tensor power. For every w in W(q,m;L,G), both maps also send the nested canonical CW basis vector named by w to the nested MM basis vector with exactly the same positionwise channel coordinates.\n\nThis is the source-faithful tensor-power bridge needed before the separate zeroing projector selects the prescribed family and deletes all other channel words.\n\n**Formalization Note** The statement includes the complete tensor identities and exact basis laws for both the 022 orientation and its 202 mode rotation; it does not claim the subsequent coordinate-selection projector.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 (PDF pp. 59–60 / printed pp. 58–59) and Appendix A, proof of Lemma 4.6(c) (PDF pp. 82–83 / printed pp. 81–82), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words

open PiTensorProduct
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false

theorem mme_dwz_cw_square_central_022_202_restricted_word_power_router
    (K : Type u) [Field K] (q m L G : ℕ) :
    (exists maps022 : ∀ s : Fin 3,
        ((Central022Block K q).kronPow m).V s →ₗ[K]
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m).V s,
      PiTensorProduct.map maps022 ((Central022Block K q).kronPow m).t =
          ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps022 s
            (central022SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          central022MMWordVec K q m
            (encodeCentralRestricted022Word w) s) ∧
    (exists maps202 : ∀ s : Fin 3,
        ((Central202Block K q).kronPow m).V s →ₗ[K]
          ((MMObj K (q ^ 2 + 2) 1 1).kronPow m).V s,
      PiTensorProduct.map maps202 ((Central202Block K q).kronPow m).t =
          ((MMObj K (q ^ 2 + 2) 1 1).kronPow m).t ∧
      ∀ (w : CentralRestricted022Word q m L G) (s : Fin 3),
        maps202 s
            (central202SourceWordVec K q m
              (encodeCentralRestricted022Word w) s) =
          central202MMWordVec K q m
            (encodeCentralRestricted022Word w) s) := by
  sorry
