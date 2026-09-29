-- Prove2me | Theorems.Thm_mme_dwz_cw_square_central_022_202_source_router
-- name    : mme_dwz_cw_square_central_022_202_source_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:48:38.793145+00:00
-- url     : https://prove2.me/theorems/2ccab26a-a38d-4c1a-9648-0be920d22692
-- title:
--   Source-faithful routers for the central 022 and 202 constituents of the CW square
-- statement:
--   Let $T_q$ be the Coppersmith–Winograd tensor over a field $K$, and equip $T_q\otimes T_q$ with its canonical five-grading. The central constituents of grades $(0,2,2)$ and $(2,0,2)$ admit explicit modewise linear maps to standard matrix-multiplication tensors:
--
--   $$
--   (T_q\otimes T_q)_{0,2,2}\longrightarrow \langle 1,1,q^2+2\rangle,
--   \qquad
--   (T_q\otimes T_q)_{2,0,2}\longrightarrow \langle q^2+2,1,1\rangle.
--   $$
--
--   Each map sends the complete graded block tensor to the corresponding matrix-multiplication tensor. Moreover, it preserves the exact source-channel labels: the two exceptional CW basis-pair channels and every ordered-pair channel $(i,j)\in[q]^2$ are sent to their prescribed common coordinate in $[q^2+2]$ in all three modes.
--
--   This strengthens a dimension-only restriction certificate by identifying the actual canonical CW source coordinates. It is the one-letter semantic input needed to lift the central restrictions through tensor powers and then zero prescribed channel words in square-laser constructions.
--
--   **Formalization Note** The theorem simultaneously returns the 022 and mode-rotated 202 maps and states their action on every canonical basis pair through the shared fine-channel interface.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 (PDF pp. 59–60 / printed pp. 58–59) and Appendix A, proof of Lemma 4.6(c) (PDF pp. 82–83 / printed pp. 81–82), https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_cw_square_fine_central_channels

open PiTensorProduct
open MME
open MME.DWZFineChannel

universe u

theorem mme_dwz_cw_square_central_022_202_source_router
    (K : Type u) [Field K] (q : ℕ) :
    (∃ maps022 : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K q).classOf s
            (cwSquareBlockType 0 2 2 s) →ₗ[K]
          (MMObj K 1 1 (q ^ 2 + 2)).V s,
      PiTensorProduct.map maps022
          ((cwSquareCanonicalGrading K q).blockTensor
            (cwSquareBlockType 0 2 2)) =
        MMTensor K 1 1 (q ^ 2 + 2) ∧
      ∀ (c : Fine022Channel q) (s : Fin 3),
        maps022 s
            ((cwSquareCanonicalGrading K q).blockProj s
              (cwSquareBlockType 0 2 2 s)
              (cwSquareCanonicalBasis K q s (fine022SourcePair q c s))) =
          fine022MMVec K q (fine022ChannelEquiv q c) s) ∧
    (∃ maps202 : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K q).classOf s
            (cwSquareBlockType 2 0 2 s) →ₗ[K]
          (MMObj K (q ^ 2 + 2) 1 1).V s,
      PiTensorProduct.map maps202
          ((cwSquareCanonicalGrading K q).blockTensor
            (cwSquareBlockType 2 0 2)) =
        MMTensor K (q ^ 2 + 2) 1 1 ∧
      ∀ (c : Fine202Channel q) (s : Fin 3),
        maps202 s
            ((cwSquareCanonicalGrading K q).blockProj s
              (cwSquareBlockType 2 0 2 s)
              (cwSquareCanonicalBasis K q s (fine202SourcePair q c s))) =
          fine202MMVec K q (fine202ChannelEquiv q c) s) := by
  sorry
