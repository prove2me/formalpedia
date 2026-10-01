-- Prove2me | Theorems.Thm_burau_rho_mul_Sm_of_zero
-- name    : burau_rho_mul_Sm_of_zero
-- status  : Proved
-- author  : @lt9
-- created : 2026-10-01T00:06:58.140592+00:00
-- url     : https://prove2.me/theorems/0c6bd612-2b91-4abb-9aa5-bb52ccfdaf9d
-- title:
--   The S-rule in the terminal case M_00 = 0
-- statement:
--   **The $S$-rule in the terminal case $M_{00}=0$.** Let $M$ be a unimodular $2\times2$ integer matrix
--   with $M_{00}=0$, so that $M=\left(\begin{smallmatrix}0&\pm1\\\mp1&d\end{smallmatrix}\right)$ and
--   $M\cdot S=\left(\begin{smallmatrix}\pm1&0\\d&\mp1\end{smallmatrix}\right)$. Then the descent of $M\cdot S$
--   takes exactly one step, landing on $(M\cdot S)\cdot S$, and
--   $$ \rho\bigl(M\cdot S\bigr) = \mathtt{baseQ}\bigl((M\cdot S)\cdot S\bigr)\cdot \mathrm{liftS}^{-1}. $$
--   This is one of the two cases of the $S$-rule $\rho(M\cdot S)=\rho(M)\cdot\mathrm{liftS}$ that are proved;
--   it shows that in the terminal branch the rule reduces to a statement about the two explicit `baseQ`
--   values, which is the content of the terminal-case nodes.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

theorem burau_rho_mul_Sm_of_zero (M : BurauNC.M2) (hd : M.det = 1) (h0 : M 0 0 = 0) :
    BurauNC.rho (M * BurauNC.Sm) =
      BurauNC.baseQ (M * BurauNC.Sm * BurauNC.Sm) * BurauNC.liftS⁻¹ := by sorry
