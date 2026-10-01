-- Prove2me | Theorems.Thm_burau_rho_mul_Sm_of_L_rule
-- name    : burau_rho_mul_Sm_of_L_rule
-- status  : Open
-- author  : @lt9
-- created : 2026-10-01T06:46:26.417179+00:00
-- url     : https://prove2.me/theorems/dedcc384-fc11-4f21-87db-123f56b5f129
-- title:
--   The S-rule from the L-rule
-- statement:
--   **The milestone's $S$-rule follows from the $L$-rule.** If the descent section $\rho$ is
--   multiplicative against $L^k$ for every unimodular $X$ and every $k$, then it is
--   multiplicative against $S$: $\rho(M\,S)=\rho(M)\,\mathrm{liftS}$ for every unimodular $M$. The descent relation $M S = N\,L^{-e}$ turns the $S$-rule at $M$ into the $L$-rule at the successor $N$ with $e=M_{01}/M_{00}$.
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

theorem burau_rho_mul_Sm_of_L_rule
    (hL : ∀ X : BurauNC.M2, X.det = 1 → ∀ k : ℤ,
      BurauNC.rho (X * BurauNC.Lm k) =
        BurauNC.rho X * BurauNC.liftS⁻¹ * BurauNC.liftT ^ (-k) * BurauNC.liftS) :
    ∀ M : BurauNC.M2, M.det = 1 →
      BurauNC.rho (M * BurauNC.Sm) = BurauNC.rho M * BurauNC.liftS := by sorry
