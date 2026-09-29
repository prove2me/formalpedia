-- Prove2me | solution 1 for mme_stothers_phi116_profile_extraction_of_exact_address_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:54:20.059978+00:00
-- url     : https://prove2.me/submissions/871cfdd7-0806-4162-bfcd-34e8728f4ca5

import Theorems.Thm_mme_stothers_phi116_exact_address_cyclic_value_below
import Theorems.Thm_mme_stothers_phi116_outer_hashing_from_address_cyclic_values

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau a : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (haPos : 0 < a) (haLt : a < 1)
    (hfactor :
      ∀ {N alpha beta : ℕ}, alpha + beta = N →
        ∀ address : CWQ6ExactCoupledAddress N alpha beta,
          TensorObj.Restrict
            (TensorObj.kronFin 4 (fun r ↦
              (MME.StothersFourth.Phi116.phi116ComponentObj K r).kronPow
                (MME.StothersFourth.Phi116.phi116ComponentMultiplicity
                  alpha beta r)))
            (gradedAddressBlock
              (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K)
              address.1)) :
    ∀ V : Real, 0 ≤ V →
      V < 4 *
        (((2 * MME.StothersFourth.L 6 tau) / a) ^ a *
          ((MME.StothersFourth.E 6 tau ^ (2 : ℕ)) / (1 - a)) ^
            (1 - a)) →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  apply mme_stothers_phi116_outer_hashing_from_address_cyclic_values
    tau a htauLower htauUpper haPos haLt
  intro N alpha beta hsum address W hWpos hWcoupled hWrect
  exact mme_stothers_phi116_exact_address_cyclic_value_below
    tau htauLower address (hfactor hsum address) W hWpos hWcoupled hWrect
