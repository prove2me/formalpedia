-- Prove2me | Theorems.Thm_mme_CW_square_laser_value_below_2376_of_coupled_below
-- name    : mme_CW_square_laser_value_below_2376_of_coupled_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:16:32.383996+00:00
-- url     : https://prove2.me/theorems/478a9b3f-ac15-460e-89f5-9039354499b4
-- title:
--   CW tensor-square tau-values strictly below the exact 2.376 auxiliary rate
-- statement:
--   Fix $q=6$, $3\tau\ge2$, and the exact rational profile of the Coppersmith--Winograd $2.376$ certificate. Assume that every nonnegative cyclic coupled value strictly below
--
--   $$
--   C(\tau)=4\,6^{3\tau}(6^{3\tau}+2)
--   $$
--
--   is attained by concrete asymptotic tau-value witnesses for the cyclic symmetrization of the coupled $(1,1,2)$ constituent. Then every nonnegative value $V$ satisfying
--
--   $$
--   V<\operatorname{auxiliaryRHS}(6,\tau,a,b,c,d),
--   \qquad
--   (a,b,c,d)=\frac{(699,37518,307638,616627)}{3{,}000{,}000},
--   $$
--
--   is attained by the tensor square $T_6\otimes T_6$.
--
--   The strict inequalities are essential. The five-grade type selection, Stirling estimates, and Salem--Spencer collision pruning lose a factor $\exp(-o(N))$ at power $N$. Any fixed gap below the displayed exponential rate absorbs that loss, whereas equality at the boundary would assert a stronger constant-relative attainment statement not supplied by the source. The conclusion still uses the concrete tau-value predicate, so its witnesses retain actual finite direct-sum tensor restrictions.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square extraction, equations (11)--(13), Stirling estimates, Salem--Spencer pruning, and auxiliary inequality on journal pp. 265--269 (PDF pp. 15--19), together with the coupled lemma on journal pp. 270--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME
universe u

theorem mme_CW_square_laser_value_below_2376_of_coupled_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      ∀ Vc : ℝ, 0 ≤ Vc →
        Vc <
          4 * (6 : ℝ) ^ (3 * tau) *
            ((6 : ℝ) ^ (3 * tau) + 2) →
        HasTauValueAtLeast
          (cyclicSymmetrization (coupledObj K 6)) tau Vc)
    (V : ℝ) (hV_nonneg : 0 ≤ V)
    (hV_lt :
      V < auxiliaryRHS 6 tau
        cw2376_a cw2376_b cw2376_c cw2376_d) :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau V := by sorry
