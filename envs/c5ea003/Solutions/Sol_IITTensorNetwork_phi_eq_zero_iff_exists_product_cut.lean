-- Prove2me | solution 1 for IITTensorNetwork.phi_eq_zero_iff_exists_product_cut
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T05:51:45.304986+00:00
-- url     : https://prove2.me/submissions/0f66ccdf-7b31-4304-a08a-bd39d3433752

import Theorems.Thm_IntegratedInformation_phi_eq_zero_iff
import Theorems.Thm_IITTensorNetwork_mutualInformation_eq_zero_iff_schmidtRank_eq_one
import Definitions.Def_Novelty_IITTensorNetworkPhi

open Finset Matrix
open scoped ComplexOrder
open IITTensorNetwork

variable {n d : ℕ}
variable {psi : (Fin n → Fin d) → ℂ}

theorem solution (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) :
    Phi hpsi hn = 0 ↔
      ∃ p : Fin (n - 1),
        schmidtRank (chainCutMatrix psi ((p : ℕ) + 1)
          (by have := p.isLt; omega)) = 1 := by
  rw [show Phi hpsi hn = IntegratedInformation.Phi
    (chainCausalStructure hpsi hn) by rfl]
  rw [IntegratedInformation.phi_eq_zero_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    exact (mutualInformation_eq_zero_iff_schmidtRank_eq_one
      (normalized_chainCutMatrix hpsi _ _)).mp hp
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    exact (mutualInformation_eq_zero_iff_schmidtRank_eq_one
      (normalized_chainCutMatrix hpsi _ _)).mpr hp

#print axioms solution
