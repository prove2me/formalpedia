-- Prove2me | Theorems.Thm_mme_CW_2376_induced_family_direct_sum_extraction
-- name    : mme_CW_2376_induced_family_direct_sum_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:18:47.505467+00:00
-- url     : https://prove2.me/theorems/dfe29511-175b-4602-bc00-2346e2b5b849
-- title:
--   Direct-sum extraction from an induced exact CW profile family
-- statement:
--   Fix a field $K$, the concrete five-grade orbit certificate for $T_6\otimes T_6$, an exact-profile scale $m$, and an induced mode-disjoint family $F$ of profile addresses. Variable zeroing extracts $|F|$ independent copies of the exact CW profile core from the tensor-square power:
--
--   $$
--   \langle |F|\rangle\otimes \operatorname{Core}_m\;\le\;(T_6\otimes T_6)^{\otimes 3{,}000{,}000m}.
--   $$
--
--   Each retained address has the fifteen multiplicities of equation (13). Mode-disjointness makes the retained blocks independent in every tensor mode, while inducedness rules out every supported mixed block assembled from different retained addresses. The coupled $(1,1,2)$, $(2,1,1)$, and $(1,2,1)$ constituents are grouped in equal numbers and handled by the cyclic coupled certificate.
--
--   This is the finite tensor-extraction core of the outer laser step; the Salem--Spencer counting estimate is deliberately separate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square constituents (11) on journal pp. 265--266 and exact-profile variable zeroing using (12)--(13) on pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_profile_induced_family
import Definitions.Def_mme_CW_square_five_grade_certificate
open MME
universe u

theorem mme_CW_2376_induced_family_direct_sum_extraction
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    TensorObj.Restrict
      (TensorObj.kron (TensorObj.diagObj K 3 F.card)
        (cw2376ProfileCore K m))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
        (cw2376ProfileLength m)) := by
  sorry
