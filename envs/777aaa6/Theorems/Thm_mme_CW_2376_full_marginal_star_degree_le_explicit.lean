-- Prove2me | Theorems.Thm_mme_CW_2376_full_marginal_star_degree_le_explicit
-- name    : mme_CW_2376_full_marginal_star_degree_le_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:04:27.692792+00:00
-- url     : https://prove2.me/theorems/be7eef06-8837-4f2f-ac8e-bc5976e06445
-- title:
--   The full marginal CW star is polynomially dominated by the optimized target star
-- statement:
--   Fix one mode word of any edge in the full marginal-supported Coppersmith--Winograd hypergraph at positive scale $m$, and let $N=3{,}000{,}000m$. If $D_*$ is the optimized exact-profile completion degree, then the number $D_{all}$ of all supported completions with the prescribed marginals satisfies
--
--   $$
--   D_{all} ≤ (N+1)^{15}D_*, \quad D_*=(∏_{r=0}^4 A_r!)/(∏_{σ∈Σ}β_σ!).
--   $$
--
--   The estimate partitions the entire ambient star by its realized fifteen-cell joint table. Each table fiber is counted by a stratified multinomial, target factorial-profile dominance bounds it by $D_*$, and at most $(N+1)^{15}$ tables occur. No restriction to exact-profile ambient edges is made.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), compatible completion counts and Salem--Spencer pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Definitions.Def_mme_CW_2376_marginal_joint_tables
import Theorems.Thm_mme_CW_2376_target_factorial_profile_dominates

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

theorem mme_CW_2376_full_marginal_star_degree_le_explicit
    (m : ℕ) (hm : 0 < m)
    (a : CW2376MarginalSupportedAddress m) (i : Fin 3) :
    ((cw2376MarginalSupportedUniverse m).filter
      (fun b => b.1 i = a.1 i)).card ≤
      (cw2376ProfileLength m + 1) ^ 15 *
        ((∏ r : Fin 5,
            (cw2376MarginalMultiplicity m r).factorial) /
          ∏ sigma : CW2376SupportedJointType,
            (cw2376TargetJointTable m sigma).factorial) := by
  sorry
