-- Prove2me | Theorems.Thm_mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
-- name    : mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:23:52.022997+00:00
-- url     : https://prove2.me/theorems/1166d7f7-28f5-4617-9182-1374cec403a3
-- title:
--   Exact fixed-mode fibre cardinality for phi_224
-- statement:
--   Fix a valid exact $\varphi_{224}$ profile and one of the three tensor modes. For any exact-profile word $w$, the number of exact-profile words inducing the same grade word as $w$ in that mode is
--
--   $$
--   \prod_{s=0}^{4}
--   +\frac{m_{i,s}!}{\prod_{r:\,p_i(r)=s} k_r!},
--   $$
--
--   where $k_r$ is the prescribed multiplicity of fine type $r$, $p_i(r)$ is its grade in mode $i$, and $m_{i,s}=\sum_{p_i(r)=s}k_r$ is the corresponding marginal multiplicity. In particular, this fibre size is independent of the chosen realized mode word.
--
--   This exact regularity formula supplies the target-mode degree in the finite type-2 hypergraph and allows global profile counts to be converted into local hashing degrees.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and the type-2 counting argument in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_exact_profile_marginals
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N)
    (w : MME.StothersFourth.Phi224.ExactProfileWord
      N alpha beta gamma delta)
    (i : Fin 3) :
    Nat.card
        {v : MME.StothersFourth.Phi224.ExactProfileWord
            N alpha beta gamma delta //
          MME.StothersFourth.Phi224.modeWord v.1 i =
            MME.StothersFourth.Phi224.modeWord w.1 i} =
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (MME.StothersFourth.Phi224.profileMultiplicity
              alpha beta gamma delta r.1).factorial := by
  sorry
