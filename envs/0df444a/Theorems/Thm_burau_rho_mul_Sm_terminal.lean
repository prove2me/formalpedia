-- Prove2me | Theorems.Thm_burau_rho_mul_Sm_terminal
-- name    : burau_rho_mul_Sm_terminal
-- status  : Proved
-- author  : @lt9
-- created : 2026-10-01T00:18:53.634856+00:00
-- url     : https://prove2.me/theorems/420957ed-a2ae-49e8-ad0f-e52158c6b48b
-- title:
--   The S-rule in the terminal case
-- statement:
--   **The $S$-rule in the terminal case.** For a unimodular $2\times2$ integer matrix $M$ with
--   $M_{00}=0$,
--   $$ \rho\bigl(M\cdot S\bigr) = \rho(M)\cdot \mathrm{liftS}, $$
--   where $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ and
--   $\mathrm{liftS}=\overline{\sigma_0^2\sigma_1}$. Here $M=\left(\begin{smallmatrix}0&\pm1\\\mp1&d\end{smallmatrix}\right)$,
--   $M\cdot S$ descends in one step to $-M$, and the two values of the terminal map `baseQ` differ exactly by
--   the conjugation identities $\mathrm{liftS}^3X\mathrm{liftS}^{-1}=\mathrm{liftS}X\mathrm{liftS}$ and its
--   inverse, which hold because $\mathrm{liftS}^2$ is central. With the zero case this disposes of the whole
--   terminal branch of the $S$-rule; only the branch $M_{00}\neq0$ with non-vanishing descent quotient — the
--   continued-fraction reversal — remains open.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group
import Theorems.Thm_burau_rho_mul_Sm_of_zero
import Theorems.Thm_burau_liftS_pow_four
import Theorems.Thm_burau_liftS_sq_central

set_option autoImplicit false

theorem burau_rho_mul_Sm_terminal (M : BurauNC.M2) (hd : M.det = 1) (h0 : M 0 0 = 0) :
    BurauNC.rho (M * BurauNC.Sm) = BurauNC.rho M * BurauNC.liftS := by sorry
