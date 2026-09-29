-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_hashing_from_address_values
-- name    : mme_stothers_phi116_outer_hashing_from_address_values
-- status  : Open
-- author  : @WillR
-- created : 2026-09-05T06:40:08.56786+00:00
-- url     : https://prove2.me/theorems/2acef82f-88da-4423-9125-369e447bf265
-- title:
--   Phi116 outer hashing from address-wise cyclic values
-- statement:
--   This interface isolates the address-hashing step for the $\varphi_{116}$ constituent. Suppose every exact coupled address admits a cyclic tau-value lower bound obtained by assigning four positive component weights: two are bounded by $L(\tau)$ and two by $E(\tau)^2$, with exponents determined by the address multiplicities. If $0<a<1$, then the address-wise bounds combine with the marginal entropy estimate to show that every nonnegative $V$ below the displayed outer-hashing expression is a tau-value of the cyclically symmetrized fourth-power constituent. The theorem is the reusable bridge from local exact-address values to the global outer-hashing conclusion.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5, Lemma 5.1 and the phi116 outer-hashing extraction; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_outer_hashing_from_address_values
    {K : Type u} [Field K] (tau a : Real)
    (haPos : 0 < a) (haLt : a < 1)
    (haddress :
      ∀ {N alpha beta : ℕ}, alpha + beta = N →
        ∀ address : CWQ6ExactCoupledAddress N alpha beta,
          ∀ W : Fin 4 → ℝ,
            (∀ r, 0 < W r) →
            (W 0 < MME.StothersFourth.L 6 tau ∧
              W 1 < MME.StothersFourth.L 6 tau) →
            (W 2 < MME.StothersFourth.E 6 tau ^ (2 : ℕ) ∧
              W 3 < MME.StothersFourth.E 6 tau ^ (2 : ℕ)) →
            HasTauValueAtLeast
              (cyclicSymmetrization
                (gradedAddressBlock
                  (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K)
                  address.1)) tau
              (∏ r : Fin 4,
                (W r ^
                  MME.StothersFourth.Phi116.phi116ComponentMultiplicity
                    alpha beta r) / 2)) :
    ∀ V : Real, 0 ≤ V →
      V < 4 *
        (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
          ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^
            (1 - a)) →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  sorry
