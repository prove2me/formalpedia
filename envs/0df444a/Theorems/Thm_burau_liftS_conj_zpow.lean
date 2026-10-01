-- Prove2me | Theorems.Thm_burau_liftS_conj_zpow
-- name    : burau_liftS_conj_zpow
-- status  : Proved
-- author  : @lt9
-- created : 2026-10-01T04:31:49.169422+00:00
-- url     : https://prove2.me/theorems/d425d8e9-10fc-4102-aa12-cdd55a7e2b31
-- title:
--   Conjugating t by s is symmetric
-- statement:
--   **Conjugating $t$ by $s$ is symmetric.** In the group
--   $Q=\overline{B_3/\langle\langle\Delta^4\rangle\rangle}\cong \mathrm{SL}(2,\mathbb Z)$, with
--   $s=\mathrm{liftS}$ and $t=\mathrm{liftT}$ the lifts of $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$
--   and $T=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$, one has
--   $$ s\,t^n\,s^{-1} = s^{-1}\,t^n\,s \qquad (n\in\mathbb Z). $$
--   Both sides lift the same element of $\mathrm{SL}(2,\mathbb Z)$: the left conjugates $T^n$ by $S$, the
--   right by $S^{-1}=S^3$, and $STS^{-1}=L^n=S^{-1}T^nS$ because $S^2=-1$ is central in $\mathrm{SL}(2,\mathbb Z)$.
--   The formal proof only needs that $\mathrm{liftS}^2$ is central in $Q$ (the Proved node
--   `burau_liftS_sq_central`), together with cancellation of $\mathrm{liftS}$. This identity is the
--   technical heart of the class-by-class analysis of the $S$-rule: it is what makes the terminal
--   correction factors of the descent section cancelling out.
-- source:
--   Euclidean algorithm in SL(2,Z), the reduced Burau representation, and the amalgam SL(2,Z) = Z/4 *_{Z/2} Z/6; cf. H. S. M. Coxeter and W. O. J. Moser, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_reduced_braid_group
import Theorems.Thm_burau_liftS_sq_central

set_option autoImplicit false

theorem burau_liftS_conj_zpow (n : ℤ) :
    BurauNC.liftS * BurauNC.liftT ^ n * BurauNC.liftS⁻¹ =
      BurauNC.liftS⁻¹ * BurauNC.liftT ^ n * BurauNC.liftS := by sorry
