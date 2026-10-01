-- Prove2me | Theorems.Thm_burau_rho_T
-- name    : burau_rho_T
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T23:43:00.110978+00:00
-- url     : https://prove2.me/theorems/5ba00afd-0ee9-4d1c-8d8d-ae326c8d6e64
-- title:
--   The T-rule for the Euclidean descent section
-- statement:
--   **The $T$-rule for the descent section.** For every unimodular $2\times2$ integer matrix $M$ and every
--   integer $j$,
--   $$ \rho\bigl(M\cdot T^j\bigr) = \rho(M)\cdot \mathrm{liftT}^{\,j}, $$
--   where $T^j=\left(\begin{smallmatrix}1&j\\0&1\end{smallmatrix}\right)$ and
--   $\mathrm{liftT}=\overline{\sigma_0^{-1}}$ is the image of the standard generator $T$ of
--   $\mathrm{SL}(2,\mathbb Z)$ in the reduced braid quotient $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$.
--   This is one of the two multiplication rules that turn the Euclidean descent section into a group-theoretic
--   section of $q:B_3\to Q$; the companion $S$-rule $\rho(M\cdot S)=\rho(M)\cdot\mathrm{liftS}$ is the
--   continued-fraction identity isolated by this project.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

theorem burau_rho_T (M : BurauNC.M2) (j : ℤ) (hd : M.det = 1) :
    BurauNC.rho (M * BurauNC.Tm j) = BurauNC.rho M * BurauNC.liftT ^ j := by sorry
