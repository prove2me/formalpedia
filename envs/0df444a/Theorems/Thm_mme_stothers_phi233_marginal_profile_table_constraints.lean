-- Prove2me | Theorems.Thm_mme_stothers_phi233_marginal_profile_table_constraints
-- name    : mme_stothers_phi233_marginal_profile_table_constraints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:42:09.714629+00:00
-- url     : https://prove2.me/theorems/4a5ec452-0cc1-4a88-8625-cff2367d4ead
-- title:
--   Total and marginals of a phi_233 completion profile table
-- statement:
--   The ten-entry joint table of every same-marginal $\varphi_{233}$ completion has total mass $2N$, and its projection along each of the three modes is exactly the prescribed five-grade marginal. Explicitly, if $k_r$ counts coordinates of supported pattern $r$, then
--
--   $$
--   \sum_{r=0}^{9}k_r=2N,\qquad\sum_{r:\,\operatorname{pattern}(r)_l=s}k_r=m_{l,s}.
--   $$
--
--   This holds for every mode $l$ and grade $s$. These compatibility equations justify applying the exact profile-stratum and fixed-mode conditional multinomial counts to every realized table in the ambient family.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, the same-marginal completion constraints for phi_233 in Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_marginal_profile_table

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_marginal_profile_table_constraints
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.MarginalAddress
      N alpha beta gamma delta) :
    (∑ r : Fin 10,
      MME.StothersFourth.Phi233.marginalProfileTable a r) = 2 * N ∧
    ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 10 //
          MME.StothersFourth.Phi233.pattern r l = s},
        MME.StothersFourth.Phi233.marginalProfileTable a r.1) =
      MME.StothersFourth.Phi233.marginalMultiplicity
        alpha beta gamma delta l s := by
  sorry
