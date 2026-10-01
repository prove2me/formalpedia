-- Prove2me | Theorems.Thm_burau_rho_eq_rho_step
-- name    : burau_rho_eq_rho_step
-- status  : Open
-- author  : @lt9
-- created : 2026-10-01T06:39:28.373972+00:00
-- url     : https://prove2.me/theorems/fc326b6d-22a7-4697-81da-95c8c42fe002
-- title:
--   One descent step of the section rho
-- statement:
--   **One step of the Euclidean descent for the section $\rho$.** If $M_{00}\neq0$ then
--   $$\rho(M)=\rho\bigl((M\,T^{-n})S\bigr)\,\mathrm{liftS}^{-1}\,\mathrm{liftT}^{n},\qquad n=M_{01}/M_{00}.$$
--   This is the recursion the section is defined by, isolated as a reusable rewrite.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_srule_defs
import Definitions.Def_burau_srule_defs2
import Theorems.Thm_burau_rho_T
import Theorems.Thm_burau_liftS_conj_zpow
import Theorems.Thm_burau_rho_mul_Sm_terminal

set_option autoImplicit false

open BurauNC

theorem burau_rho_eq_rho_step (M : BurauNC.M2) (h0 : M 0 0 ≠ 0) :
    BurauNC.rho M =
      BurauNC.rho ((M * BurauNC.Tm (-(M 0 1 / M 0 0))) * BurauNC.Sm) *
        BurauNC.liftS⁻¹ * BurauNC.liftT ^ (M 0 1 / M 0 0) := by sorry
