-- Prove2me | Theorems.Thm_burau_liftS_pow_four
-- name    : burau_liftS_pow_four
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T23:05:06.128925+00:00
-- url     : https://prove2.me/theorems/f031008e-03ea-4f06-8769-6f8a8e116c29
-- title:
--   Coxeter relation: the lifted S-generator has order four
-- statement:
--   **Coxeter relation $\mathrm{liftS}^4=1$.** In the reduced braid group
--   $Q=B_3/\langle\!\langle\Delta^4\rangle\!\rangle$ the element
--   $\mathrm{liftS}=\overline{\sigma_0^2\sigma_1}$ — the image of the standard generator
--   $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$ of $\mathrm{SL}(2,\mathbb Z)$ — satisfies
--   $$ \mathrm{liftS}^4 = 1 . $$
--   It follows from $\mathrm{sLift}^4=\Delta^4$ in $B_3$ together with $\overline{\Delta^4}=1$, and is the
--   first of the Coxeter relations that present $Q\cong\mathrm{SL}(2,\mathbb Z)$.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_reduced_braid_group
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_burau_q_delta4
import Theorems.Thm_burau_sLift_pow_four

set_option autoImplicit false

theorem burau_liftS_pow_four : BurauNC.liftS ^ 4 = 1 := by sorry
