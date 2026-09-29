-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_hashing_from_address_cyclic_values
-- name    : mme_stothers_phi116_outer_hashing_from_address_cyclic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:50:40.573091+00:00
-- url     : https://prove2.me/theorems/3f0ab03b-75a8-4992-ade1-64fe2151cf20
-- title:
--   Phi_116 outer four-edge hashing from exact-address cyclic values
-- statement:
--   Fix a legal profile frequency $0<a<1$. Assume every exact supported $\varphi_{116}$ address of profile $(\alpha,\beta)$ has its expected cyclic tau-value for arbitrary strict recursive targets below $L$ and rectangular targets below $E^2$, with only the explicit constant factor $1/16$. Then every nonnegative value below the two-type rate $$4\left(\frac{2L}{a}\right)^a\left(\frac{E^2}{1-a}\right)^{1-a}$$ is attained by the cyclically symmetrized literal constituent. This theorem isolates the outer asymmetric four-edge hash, balanced type count, loss absorption, and cofinal limit from all inner address-factor algebra.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21; A. M. Davie and A. J. Stothers (2013), Lemma 5.1(i).

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi116_exact_address_factorization_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_outer_hashing_from_address_cyclic_values
    {K : Type u} [Field K] (tau a : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
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
