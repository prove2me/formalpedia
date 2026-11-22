-- Prove2me | Theorems.Thm_mme_dwz_fourth_value_surplus_witness
-- name    : mme_dwz_fourth_value_surplus_witness
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-15T18:37:29.352048+00:00
-- url     : https://prove2.me/theorems/6e4324a5-5356-4bd3-9b32-7554b0182fe6
-- title:
--   DWZ fourth-power surplus certificate witness
-- statement:
--   For the Davie--Stothers fourth-power tensor $T = \mathrm{CW}_5^{\otimes 4}$ over a field $K$, with $\tau = 790643/1000000$, there exist positive integers $A$, $H$, $\mathrm{vol}$ and a real number $V > 2401$ such that
--
--   $$
--   V^6 < A^3 H^2 (\mathrm{vol}^3)^{\tau}.
--   $$
--
--   The paired tensor $T \otimes T^{\mathrm{swap}}$ (where $\mathrm{swap}$ exchanges the first two modes) admits a finite $C$-tensor family certificate with parameters $A$, $H$, $\mathrm{vol}$.
--
--   This is the Table 3 numerical witness step in Duan--Wu--Zhou: the certificate feeds the paired certificate-to-tau-value bridge, which converts the bound above into a six-symmetrized $\tau$-value strictly above $2401^6$.
--
--   **Formalization Note** Lean states the volume power as $((\mathrm{vol}^3 : \mathbb{N}) : \mathbb{R})$ and the certificate as a nonempty `CTensorOneHOneFamilyCertificate` over the Kronecker pairing of `cwFourthObj K 5` with its mode-swapped copy.
-- source:
--   Duan--Wu--Zhou 2025, New upper bounds for the matrix multiplication exponent, https://arxiv.org/abs/2210.10173v5, Section 8, Eq. (25), Table 3, p. 78

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_CTensorOneHOneFamilyCertificate

open MME

universe u

set_option autoImplicit false

theorem mme_dwz_fourth_value_surplus_witness
    {K : Type u} [Field K] :
    exists (A : Nat), exists (H : Nat), exists (volume : Nat), exists (V : Real),
      (2401 : Real) < V /\
      V ^ 6 < (A : Real) ^ 3 * (H : Real) ^ 2 *
        (((volume ^ 3 : Nat) : Real) ^ (790643 / 1000000 : Real)) /\
      Nonempty
        (CTensorOneHOneFamilyCertificate
          (TensorObj.kron (MME.StothersFourth.cwFourthObj K 5)
            (TensorObj.permObj MME.swapFirstTwoPerm (MME.StothersFourth.cwFourthObj K 5)))
          A H volume) := by sorry
