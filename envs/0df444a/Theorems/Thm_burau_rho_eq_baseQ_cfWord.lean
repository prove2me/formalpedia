-- Prove2me | Theorems.Thm_burau_rho_eq_baseQ_cfWord
-- name    : burau_rho_eq_baseQ_cfWord
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T23:54:14.715696+00:00
-- url     : https://prove2.me/theorems/79706b46-ae6e-416f-b340-aa738bc30636
-- title:
--   The descent section equals terminal value times recorded word
-- statement:
--   **The descent section is the terminal value times the recorded word.** For every $2\times2$ integer
--   matrix $M$,
--   $$ \rho(M) = \mathtt{baseQ}\bigl(\mathtt{cfEnd}(M)\bigr)\cdot \mathtt{cfWord}\bigl(\mathtt{cfList}(M)\bigr), $$
--   where $\mathtt{cfList}$ is the quotient list of the Euclidean descent, $\mathtt{cfEnd}$ is the terminal
--   matrix it reaches, $\mathtt{baseQ}$ is the explicit terminal value, and $\mathtt{cfWord}$ turns the
--   quotient list into the product of the descent factors
--   $\mathrm{liftS}^{-1}\mathrm{liftT}^{e}$ in the reduced braid quotient
--   $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$. The proof is a strong induction on the descent measure
--   $|M_{00}|$. Together with the $T$-rule this is the structural description of $\rho$ that turns the two
--   multiplication rules into a proof of $\rho(q\beta)=\beta$ for words $\beta$ in the braid group, and hence
--   into the reduction of the milestone frontier to the continued-fraction $S$-rule.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_reduced_braid_group

set_option autoImplicit false

theorem burau_rho_eq_baseQ_cfWord (M : BurauNC.M2) :
    BurauNC.rho M = BurauNC.baseQ (BurauNC.cfEnd M) * BurauNC.cfWord (BurauNC.cfList M) :=
  by sorry
