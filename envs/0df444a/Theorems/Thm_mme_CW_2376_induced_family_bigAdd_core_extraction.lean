-- Prove2me | Theorems.Thm_mme_CW_2376_induced_family_bigAdd_core_extraction
-- name    : mme_CW_2376_induced_family_bigAdd_core_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:26:44.758464+00:00
-- url     : https://prove2.me/theorems/526d8724-b2fd-4339-b442-ac97f7829e9a
-- title:
--   Independent profile-core blocks from an induced CW family
-- statement:
--   Fix the five-grade orbit certificate for $T_6\otimes T_6$ and an induced, mode-disjoint family $F$ of exact-profile addresses at scale $m$. The corresponding profile-core blocks form a genuine direct sum inside the tensor-square power:
--
--   $$
--   \bigoplus_{x\in F}\operatorname{Core}_m\;\le\;(T_6\otimes T_6)^{\otimes 3{,}000{,}000m}.
--   $$
--
--   The exact multiplicities in each address identify its block with the profile core. Mode-disjointness separates the selected variables in every tensor mode, while inducedness ensures that variable zeroing leaves no mixed supported block from different members of $F$.
--
--   This direct-sum form is the most convenient interface for the generic independent-block restriction theorem; a separate tensor-isomorphism turns it into $\langle|F|\rangle\otimes\operatorname{Core}_m$.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square constituents (11) on journal pp. 265--266 and exact-profile variable zeroing using (12)--(13) on pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_profile_induced_family
import Definitions.Def_mme_CW_square_five_grade_certificate
open MME
universe u

theorem mme_CW_2376_induced_family_bigAdd_core_extraction
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (fun _ : Fin F.card => cw2376ProfileCore K m))
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
        (cw2376ProfileLength m)) := by
  sorry
