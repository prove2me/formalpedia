-- Prove2me | Theorems.Thm_mme_CW_2376_fixed_mode_joint_table_fiber_card
-- name    : mme_CW_2376_fixed_mode_joint_table_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:26:40.62768+00:00
-- url     : https://prove2.me/theorems/5fed0d7b-7045-4c26-b924-62e8141df69b
-- title:
--   Exact stratified-multinomial size of a fixed-mode CW joint-table fiber
-- statement:
--   Fix a mode word in the full marginal-supported squared Coppersmith--Winograd hypergraph and a supported fifteen-cell joint table $k$ having the prescribed five-grade marginal in every mode. The number of ambient addresses that share the fixed word and realize exactly $k$ is the stratified multinomial
--
--   $$
--   \frac{\prod_{r=0}^{4} A_r!}{\prod_{\sigma\in\Sigma} k_\sigma!}.
--   $$
--
--   Here $A_r$ is the prescribed multiplicity of grade $r$, and $\Sigma$ is the set of fifteen supported joint types. This is the exact fixed-table fiber count needed to partition the full ambient star before applying factorial-profile dominance.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), compatible completion counts in the optimized profile on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Definitions.Def_mme_CW_2376_marginal_joint_tables

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem mme_CW_2376_fixed_mode_joint_table_fiber_card
    (m : ℕ) (a : CW2376MarginalSupportedAddress m) (i : Fin 3)
    (k : CW2376JointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ r : Fin 5,
      (∑ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 l = r}, k sigma.1) =
        cw2376MarginalMultiplicity m r) :
    Nat.card
        {b : CW2376MarginalSupportedAddress m //
          b.1 i = a.1 i ∧ cw2376MarginalJointTable b = k} =
      (∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial) /
        ∏ sigma : CW2376SupportedJointType, (k sigma).factorial := by
  sorry
