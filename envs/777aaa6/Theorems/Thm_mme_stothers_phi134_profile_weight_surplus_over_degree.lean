-- Prove2me | Theorems.Thm_mme_stothers_phi134_profile_weight_surplus_over_degree
-- name    : mme_stothers_phi134_profile_weight_surplus_over_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:28:59.265265+00:00
-- url     : https://prove2.me/theorems/4aeb2652-af19-4bf4-abf5-5fa8f08fbdcd
-- title:
--   Finite Phi134 profile surplus over sharp cyclic degree
-- statement:
--   Let $a,c>0$, $c\leq\sigma$, and $\sigma+a\leq1$.  For positive component bases $L,E,H$ and every nonnegative $V$ strictly below the Davie--Stothers $\phi_{134}$ profile rate
--
--   $$8\left(\frac L\sigma\right)^\sigma\left(\frac E{1-\sigma}\right)^{1-\sigma}\left(\frac1a\right)^a\left(\frac{H/2}{c}\right)^c\left(\frac E{1-a-c}\right)^{1-a-c},$$
--
--   there is a positive integral profile $\alpha+\beta+\gamma+\delta=N$ such that
--
--   $$V^{2N}D\exp\bigl(4000\sqrt{12N+1}\bigr)<T^3L^{2\beta+2\gamma}E^{2\alpha+2\beta+4\delta}H^{2\gamma}.$$
--
--   Here $T$ is the exact eight-pattern profile cardinality and $D=D_0D_1D_2$ is the sharp cyclic same-mode factorial degree.  This is the finite strict-surplus form of Lemma 5.1(iii), retaining both the actual collision degree and the explicit subexponential hashing loss.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 3.3 and Lemma 5.1(iii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi134_profile_data

open MME Real BigOperators

set_option autoImplicit false

theorem mme_stothers_phi134_profile_weight_surplus_over_degree
    (sigma a c L E H V : ℝ)
    (ha : 0 < a) (hc : 0 < c)
    (hcs : c ≤ sigma) (hsa : sigma + a ≤ 1)
    (hL : 0 < L) (hE : 0 < E) (hH : 0 < H)
    (hV : 0 ≤ V)
    (hVlt :
      V <
        8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c))) :
    ∃ N alpha beta gamma delta : ℕ,
      0 < N ∧ alpha + beta + gamma + delta = N ∧
      let D := fun t : Fin 3 ↦
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi134.marginalMultiplicity
            N alpha beta gamma delta t s).factorial /
            ∏ r : {r : Fin 8 //
                MME.StothersFourth.Phi134.pattern r t = s},
              (MME.StothersFourth.Phi134.profileMultiplicity
                alpha beta gamma delta r.1).factorial
      V ^ (2 * N) * (D 0 * (D 1 * D 2) : ℕ) *
          Real.exp (4000 * Real.sqrt ((12 * N + 1 : ℕ) : ℝ)) <
        (Nat.card
          (MME.StothersFourth.Phi134.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) ^ (3 : ℕ) *
          (L ^ (2 * beta + 2 * gamma) *
            E ^ (2 * alpha + 2 * beta + 4 * delta) *
            H ^ (2 * gamma)) := by
  sorry
