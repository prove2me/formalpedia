-- Prove2me | Theorems.Thm_mme_stothers_phi134_capacity_entropy_lower_bound
-- name    : mme_stothers_phi134_capacity_entropy_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:18:47.019967+00:00
-- url     : https://prove2.me/theorems/5055b007-9b13-4920-a435-538cda2995f5
-- title:
--   Finite entropy lower bound for Phi134 capacity
-- statement:
--   For a positive integral symmetric $\phi_{134}$ profile of length $2N$, let $T$ be its exact-profile cardinality and let $D=D_0D_1D_2$ be its sharp cyclic same-mode degree.  Put
--
--   $$a_N=\frac{\alpha}{N},\qquad c_N=\frac{\gamma}{N},\qquad s_N=\frac{\beta+\gamma}{N}$$
--
--   and
--
--   $$h_N=(3-c_N)\log2- s_N\log s_N-(1-s_N)\log(1-s_N)-a_N\log a_N-c_N\log c_N-(1-a_N-c_N)\log(1-a_N-c_N),$$
--
--   with $0\log0=0$.  Then
--
--   $$\exp(2Nh_N)\leq(6(2N+1))^{15}\frac{T^3}{D}.$$
--
--   This is the finite three-marginal capacity estimate underlying the asymptotic $\phi_{134}$ profile rate; its only loss is polynomial.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Lemma 3.3 and Lemma 5.1(iii), pp. 359–365; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Definitions.Def_mme_stothers_phi134_profile_data

open MME Real BigOperators

set_option autoImplicit false

theorem mme_stothers_phi134_capacity_entropy_lower_bound
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : alpha + beta + gamma + delta = N) :
    let D := fun t : Fin 3 ↦
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi134.marginalMultiplicity
          N alpha beta gamma delta t s).factorial /
          ∏ r : {r : Fin 8 //
              MME.StothersFourth.Phi134.pattern r t = s},
            (MME.StothersFourth.Phi134.profileMultiplicity
              alpha beta gamma delta r.1).factorial
    let degree := D 0 * (D 1 * D 2)
    Real.exp ((2 * N : ℝ) *
      (let an := (alpha : ℝ) / N
       let cn := (gamma : ℝ) / N
       let sn := ((beta : ℝ) + gamma) / N
       (3 - cn) * Real.log 2 +
         Real.negMulLog sn + Real.negMulLog (1 - sn) +
         Real.negMulLog an + Real.negMulLog cn +
         Real.negMulLog (1 - an - cn))) ≤
      (6 * ((2 * N + 1 : ℕ) : ℝ)) ^ (15 : ℕ) *
        ((Nat.card
          (MME.StothersFourth.Phi134.ExactProfileAddress
            N alpha beta gamma delta) : ℝ) ^ (3 : ℕ) /
          (degree : ℝ)) := by
  sorry
