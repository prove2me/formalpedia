-- Prove2me | Theorems.Thm_mme_stothers_phi224_fixed_mode_histogram_fiber_card
-- name    : mme_stothers_phi224_fixed_mode_histogram_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:23:42.882533+00:00
-- url     : https://prove2.me/theorems/a32b0f7e-2cd2-46cd-81f8-559284e6cb05
-- title:
--   Fixed-mode size of a compatible phi_224 histogram class
-- statement:
--   Fix one realized grade word in mode $i$ of the same-marginal $\varphi_{224}$ family, and fix any compatible fine histogram $k=(k_0,\ldots,k_8)$. The number of words with both this mode word and this fine histogram is
--
--   $$
--   \frac{\prod_{s=0}^{4}m_{i,s}!}{\prod_{r=0}^{8}k_r!},
--   $$
--
--   where $m_{i,s}$ is the prescribed multiplicity of grade $s$ in mode $i$. Equivalently, the count is the product over the five grade fibres of the corresponding multinomial refinement counts.
--
--   The formula is independent of the order of the fixed grade word. Together with the total histogram-class count, it proves exact regularity of the full same-marginal hypergraph.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), equations (3.5)--(3.6) and the type-2 counting argument in Lemma 5.1(iv), pp. 359--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem mme_stothers_phi224_fixed_mode_histogram_fiber_card
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi224.MarginalProfileWord
      N alpha beta gamma delta)
    (i : Fin 3) (k : Fin 9 → ℕ)
    (hkMarginal : ∀ l : Fin 3, ∀ s : Fin 5,
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r l = s}, k r.1) =
        MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta l s) :
    Nat.card
        {b : MME.StothersFourth.Phi224.MarginalProfileWord
            N alpha beta gamma delta //
          MME.StothersFourth.Phi224.modeWord b.1 i =
              MME.StothersFourth.Phi224.modeWord a.1 i ∧
            ∀ r : Fin 9,
              Fintype.card {j : Fin (2 * N) // b.1 j = r} = k r} =
      (∏ s : Fin 5,
          (MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s).factorial) /
        ∏ r : Fin 9, (k r).factorial := by
  sorry
