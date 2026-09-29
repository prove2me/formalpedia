-- Prove2me | Theorems.Thm_mme_stothers_phi233_fixed_mode_profile_table_fiber_card
-- name    : mme_stothers_phi233_fixed_mode_profile_table_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:36:39.814872+00:00
-- url     : https://prove2.me/theorems/3c99a9b8-a2c9-43ec-9d88-9b9d35af2c20
-- title:
--   Exact fixed-mode fiber of a phi_233 joint profile table
-- statement:
--   Fix one mode word of a same-marginal $\varphi_{233}$ address and fix a compatible joint table $k=(k_0,\ldots,k_9)$ on the ten supported patterns. If the projections of $k$ agree with all three prescribed five-grade marginals, then the number of same-marginal addresses having both the fixed mode word and joint table $k$ is exactly
--
--   $$
--   \frac{\prod_{s=0}^{4} m_{i,s}!}{\prod_{r=0}^{9} k_r!},
--   $$
--
--   where $m_{i,s}$ is the prescribed multiplicity of grade $s$ in the fixed mode $i$. This conditional multinomial count is the local regularity statement needed to transfer the ambient/exact entropy ratio to the mode-degree ratio used in type-2 collision pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, the same-marginal completion count in Lemma 3.3 and its application to phi_233 in Lemma 5.1(v), pp. 356--361 and 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Theorems.Thm_mme_stothers_phi233_pattern_injective

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi233_fixed_mode_profile_table_fiber_card
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta)
    (i : Fin 3) (k : Fin 10 → ℕ)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta //
          b.1 i = a.1 i ∧
            MME.StothersFourth.Phi233.marginalProfileTable b = k} =
      (∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta i s).factorial) /
        ∏ r : Fin 10, (k r).factorial := by
  sorry
