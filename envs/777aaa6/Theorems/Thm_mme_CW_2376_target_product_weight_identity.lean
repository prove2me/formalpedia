-- Prove2me | Theorems.Thm_mme_CW_2376_target_product_weight_identity
-- name    : mme_CW_2376_target_product_weight_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:32:40.820967+00:00
-- url     : https://prove2.me/theorems/e6080987-6bfb-4dd6-adf1-740041758e27
-- title:
--   Exact product form of the optimized CW joint profile
-- statement:
--   Let $s=699$, $r=37518$, $c=307638$, and $u=616627$ be the four orbit multiplicities of the optimized squared Coppersmith--Winograd profile. Set
--
--   $$
--   (q_0,q_1,q_2,q_3,q_4)=(u^2,u^2,cu,rc,sc), D=cu^4.
--   $$
--
--   For every one of the fifteen target joint types $(i,j,k)$ and every scale $m$, its prescribed multiplicity $beta_{ijk}$ satisfies
--
--   $$
--   D beta_{ijk}=m q_i q_j q_k.
--   $$
--
--   Thus the optimized joint profile is an exact integral product-form exponential family. For any competing supported joint table with the same three marginals, the corresponding product of cell weights is invariant. This supplies the exact algebraic core of the equation-(13) multinomial-dominance argument.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), optimized profile equation (13) on journal p. 268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_dominance_weights

open MME BigOperators

theorem mme_CW_2376_target_product_weight_identity
    (m : ℕ) (sigma : Fin 3 → Fin 5)
    (hsigma : sigma ∈ cw2376TargetJointTypes) :
    cw2376DominanceScale * cw2376ProfileMultiplicity m sigma =
      m * ∏ i : Fin 3, cw2376DominanceGradeWeight (sigma i) := by
  sorry
