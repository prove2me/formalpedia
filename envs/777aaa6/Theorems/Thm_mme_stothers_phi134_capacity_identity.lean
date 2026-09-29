-- Prove2me | Theorems.Thm_mme_stothers_phi134_capacity_identity
-- name    : mme_stothers_phi134_capacity_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:14:29.201583+00:00
-- url     : https://prove2.me/theorems/7d0f6a64-6850-4014-9452-56fb98115e26
-- title:
--   Exact three-mode capacity identity for Phi134
-- statement:
--   For a symmetric exact $\phi_{134}$ profile with multiplicities $(\alpha,\beta,\gamma,\delta,\delta,\gamma,\beta,\alpha)$, let $M_t$ be the multinomial count of its marginal words in mode $t$.  For each mode define
--
--   $$D_t=\prod_s\frac{m_{t,s}!}{\prod_{r:\,p_r(t)=s}m_r!},$$
--
--   where $m_{t,s}$ is the marginal count and $m_r$ is the joint-pattern count.  If $T$ is the exact-profile cardinality, then
--
--   $$M_0M_1M_2\,D_0D_1D_2=T^3.$$
--
--   Thus the same factorial product that is the sharp uniform cyclic mode-collision degree exactly converts the three marginal capacities into the cube of the target family size.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 5.1(iii), printed p. 365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Multinomial
import Definitions.Def_mme_stothers_phi134_profile_data

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi134_capacity_identity
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi134.marginalMultiplicity
          N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 //
              MME.StothersFourth.Phi134.pattern r t = s},
            (MME.StothersFourth.Phi134.profileMultiplicity
              alpha beta gamma delta r.1).factorial
    (∏ i : Fin 3,
        Nat.multinomial Finset.univ
          (MME.StothersFourth.Phi134.marginalMultiplicity
            N alpha beta gamma delta i)) *
        (D 0 * (D 1 * D 2)) =
      (Nat.card
        (MME.StothersFourth.Phi134.ExactProfileAddress
          N alpha beta gamma delta)) ^ 3 := by
  sorry
