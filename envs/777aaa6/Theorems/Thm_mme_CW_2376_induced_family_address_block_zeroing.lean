-- Prove2me | Theorems.Thm_mme_CW_2376_induced_family_address_block_zeroing
-- name    : mme_CW_2376_induced_family_address_block_zeroing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:33:15.790437+00:00
-- url     : https://prove2.me/theorems/a1ed3ab1-1cc9-4bc5-bfe9-01caaf7e1449
-- title:
--   Variable zeroing extracts the induced CW address blocks
-- statement:
--   Let $F$ be an induced, mode-disjoint family of exact five-grade addresses for the square of $T_6$. After enumerating $F$, variable zeroing extracts the direct sum of the corresponding ordered address blocks:
--
--   $$
--   \bigoplus_{a\in F} B(a)\;\le\;(T_6\otimes T_6)^{\otimes 3{,}000{,}000m}.
--   $$
--
--   Mode-disjointness makes different retained blocks use disjoint variables in each tensor mode. If a mixed block survives the coordinatewise five-grade support condition, inducedness forces its three mode words to come from the same member of $F$; hence no off-diagonal block remains.
--
--   This theorem contains only tensor-power grading, support, and variable-zeroing logic. It does not use the numerical multiplicities inside an exact address.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), support equation I+J+K=4 and variable zeroing/collision deletion on journal pp. 265 and 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_CW_2376_profile_induced_family
open MME
universe u

theorem mme_CW_2376_induced_family_address_block_zeroing
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    ∃ e : Fin F.card ≃ F,
      TensorObj.Restrict
        (TensorObj.bigAdd
          (fun j => cw2376ExactAddressBlock cert (e j).1))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
          (cw2376ProfileLength m)) := by
  sorry
