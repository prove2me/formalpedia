-- Prove2me | solution 1 for IITTensorNetwork.phi_pos_iff_all_cuts_entangled
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T05:55:39.398741+00:00
-- url     : https://prove2.me/submissions/4954d50c-460c-4922-b274-b9d7aa97bc5e

import Theorems.Thm_IntegratedInformation_phi_nonneg
import Theorems.Thm_IITTensorNetwork_phi_eq_zero_iff_exists_product_cut
import Theorems.Thm_IITTensorNetwork_schmidtRank_pos

open Finset Matrix
open scoped ComplexOrder
open IITTensorNetwork

variable {n d : ℕ}
variable {psi : (Fin n → Fin d) → ℂ}

theorem solution (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n) :
    0 < Phi hpsi hn ↔
      ∀ p : Fin (n - 1),
        2 ≤ schmidtRank (chainCutMatrix psi ((p : ℕ) + 1)
          (by have := p.isLt; omega)) := by
  constructor
  · intro hpos p
    have hne : schmidtRank (chainCutMatrix psi ((p : ℕ) + 1)
        (by have := p.isLt; omega)) ≠ 1 := by
      intro hp
      have hz : Phi hpsi hn = 0 :=
        (phi_eq_zero_iff_exists_product_cut hpsi hn).2 ⟨p, hp⟩
      linarith
    have hrank : 1 ≤ schmidtRank (chainCutMatrix psi ((p : ℕ) + 1)
        (by have := p.isLt; omega)) :=
      schmidtRank_pos (normalized_chainCutMatrix hpsi _ _)
    omega
  · intro hall
    have hnonneg : 0 ≤ Phi hpsi hn :=
      IntegratedInformation.phi_nonneg (chainCausalStructure hpsi hn)
    have hne : Phi hpsi hn ≠ 0 := by
      intro hz
      obtain ⟨p, hp⟩ := (phi_eq_zero_iff_exists_product_cut hpsi hn).1 hz
      have hp2 := hall p
      omega
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

#print axioms solution
