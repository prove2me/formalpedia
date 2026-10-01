-- Prove2me | Theorems.Thm_burau_rho_mul_Lm_of_S
-- name    : burau_rho_mul_Lm_of_S
-- status  : Proved
-- author  : @lt9
-- created : 2026-10-01T06:24:11.154277+00:00
-- url     : https://prove2.me/theorems/bbda49f4-1077-4679-9ed6-4adfce2c2962
-- title:
--   The L-rule from the S-rule
-- statement:
--   **The $L$-rule from the $S$-rule.** For a unimodular $2\times2$ integer matrix $X$, an integer
--   $k$, and $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$,
--   $L^k=\left(\begin{smallmatrix}1&0\\k&1\end{smallmatrix}\right)$: if the descent section $\rho$ is
--   multiplicative against $S$ both at $X$ and at $X L^k$, then it is multiplicative against $L^k$,
--   $$ \rho\bigl(X L^k\bigr) = \rho(X)\cdot \mathrm{liftS}^{-1}\,\mathrm{liftT}^{-k}\,\mathrm{liftS}. $$
--   The proof is the conjugation identity $L^k = S^{-1}T^{-k}S$ together with the already-established
--   $T$-rule $\rho(YT^j)=\rho(Y)\mathrm{liftT}^j$ and the symmetry
--   $\mathrm{liftS}\,\mathrm{liftT}^n\mathrm{liftS}^{-1}=\mathrm{liftS}^{-1}\mathrm{liftT}^n\mathrm{liftS}$.
--   This reformulates the milestone's $S$-rule as a one-parameter $L$-rule, which is the shape in which
--   the induction on the Euclidean descent is run.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_srule_defs
import Theorems.Thm_burau_rho_T
import Theorems.Thm_burau_liftS_conj_zpow

set_option autoImplicit false

theorem burau_rho_mul_Lm_of_S (X : BurauNC.M2) (k : ℤ) (hX : X.det = 1)
    (hS : BurauNC.rho (X * BurauNC.Sm) = BurauNC.rho X * BurauNC.liftS)
    (hk : BurauNC.rho ((X * BurauNC.Lm k) * BurauNC.Sm) =
      BurauNC.rho (X * BurauNC.Lm k) * BurauNC.liftS) :
    BurauNC.rho (X * BurauNC.Lm k) =
      BurauNC.rho X * BurauNC.liftS⁻¹ * BurauNC.liftT ^ (-k) * BurauNC.liftS := by sorry
