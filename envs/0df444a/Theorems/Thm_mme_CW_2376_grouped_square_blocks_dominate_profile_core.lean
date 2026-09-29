-- Prove2me | Theorems.Thm_mme_CW_2376_grouped_square_blocks_dominate_profile_core
-- name    : mme_CW_2376_grouped_square_blocks_dominate_profile_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:41:44.645736+00:00
-- url     : https://prove2.me/theorems/f122dcec-3d3f-4b30-b9af-6c18618f4301
-- title:
--   The grouped square constituents contain the CW profile core
-- statement:
--   Take the product of all five-grade constituents of $T_6\otimes T_6$, with each constituent raised to its exact profile multiplicity. This grouped product contains the common profile core:
--
--   $$
--   [\operatorname{Core}_m]\;\le\;\prod_{\sigma\in\{0,\ldots,4\}^3}[(T_6\otimes T_6)_\sigma]^{\mu_m(\sigma)}.
--   $$
--
--   The six rectangular types give a square matrix-multiplication side $12^{75{,}036m}$, and the three central types contribute $38^{307{,}638m}$. The three coupled types occur $616{,}627m$ times each and group into that power of the cyclic coupled constituent. The scalar types contribute tensor units, while every unsupported type has exponent zero.
--
--   This is the fixed fifteen-orbit tensor calculation; it contains neither address counting nor variable zeroing.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square constituent table following (11) on journal pp. 265--266 and exact profile (13) on pp. 267--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_rank_bridge
open MME BigOperators
universe u

theorem mme_CW_2376_grouped_square_blocks_dominate_profile_core
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6) (m : ℕ) :
    TensorQ.le
      (TensorQ.toQ (cw2376ProfileCore K m))
      (∏ σ : Fin 3 → Fin 5,
        (TensorQ.toQ (cert.grading.blockSubtensor σ)) ^
          cw2376ProfileMultiplicity m σ) := by
  sorry
