-- Prove2me | Theorems.Thm_mme_dwz_fourth_paired_cert_10M_1_1
-- name    : mme_dwz_fourth_paired_cert_10M_1_1
-- status  : Disproved
-- author  : @Tamas Fulop
-- created : 2026-09-20T20:34:28.639902+00:00
-- url     : https://prove2.me/theorems/09944270-9cae-43f8-8af7-0ec69da870d6
-- title:
--   Paired fourth-power certificate instance (A=10M, H=1, vol=1)
-- statement:
--   For the Davie--Stothers fourth-power tensor $T = CW_5^{\otimes 4}$ over a field $K$, let $T^{\mathrm{swap}}$ denote its image under the transposition of the first two modes. Then the paired tensor $T \otimes T^{\mathrm{swap}}$ admits a finite $C$-tensor family certificate with parameters
--
--   $$
--   A = 10000000, \quad H = 1, \quad \mathrm{vol} = 1.
--   $$
--
--   In Lean this is Nonempty (CTensorOneHOneFamilyCertificate (T \otimes T^{\mathrm{swap}}) 10000000 1 1). This is the tensor-construction half of the Table 3 surplus witness: combined with the elementary real inequality $2402^6 < 10000000^3$ (using $1^{\tau} = 1$) it yields the full existential witness with $V = 2402$.
--
--   **Formalization Note** Lean states the certificate over TensorObj.kron (cwFourthObj K 5) (permObj swapFirstTwoPerm (cwFourthObj K 5)) with the same module layout as mme_dwz_fourth_value_surplus_witness.
-- source:
--   Duan--Wu--Zhou 2025, New upper bounds for the matrix multiplication exponent, https://arxiv.org/abs/2210.10173v5, Section 8, Eq. (25), Table 3, p. 78; explicit reduction instance for mme_dwz_fourth_value_surplus_witness

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_CTensorOneHOneFamilyCertificate

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_paired_cert_10M_1_1
    {K : Type u} [Field K] :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (TensorObj.kron (MME.StothersFourth.cwFourthObj K 5)
          (TensorObj.permObj MME.swapFirstTwoPerm (MME.StothersFourth.cwFourthObj K 5)))
        10000000 1 1) := by sorry
