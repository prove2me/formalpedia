-- Prove2me | solution 1 for IITTensorNetwork.phi_eq_two_log_schmidtRank_iff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T05:57:53.25082+00:00
-- url     : https://prove2.me/submissions/fe321a72-3ba2-45cd-a7e4-60e5e6dd2955

import Theorems.Thm_IITTensorNetwork_entanglementEntropy_eq_log_schmidtRank_iff
import Theorems.Thm_IITTensorNetwork_mutualInformation_eq_two_mul_entanglementEntropy_general
import Theorems.Thm_IITTensorNetwork_mutualInformation_le_two_log_schmidtRank
import Theorems.Thm_IITTensorNetwork_phi_le_mutualInformation
import Theorems.Thm_IITTensorNetwork_le_phi
import Theorems.Thm_IITTensorNetwork_exists_minimal_cut

open Finset Matrix
open scoped ComplexOrder
open IITTensorNetwork

variable {n d : ℕ} {psi : (Fin n → Fin d) → ℂ}

theorem solution (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) (hn : 2 ≤ n)
    (p : Fin (n - 1)) :
    Phi hpsi hn
        = 2 * Real.log (schmidtRank (chainCutMatrix psi ((p : ℕ) + 1)
            (by have := p.isLt; omega))) ↔
      (FlatSchmidtSpectrum (chainCutMatrix psi ((p : ℕ) + 1)
          (by have := p.isLt; omega)) ∧
        ∀ q : Fin (n - 1),
          2 * Real.log (schmidtRank (chainCutMatrix psi ((p : ℕ) + 1)
              (by have := p.isLt; omega)))
            ≤ mutualInformation (chainCutMatrix psi ((q : ℕ) + 1)
              (by have := q.isLt; omega))) := by
  let M := chainCutMatrix psi ((p : ℕ) + 1) (by have := p.isLt; omega)
  have hM : Normalized M := normalized_chainCutMatrix hpsi _ _
  have hsat : mutualInformation M = 2 * Real.log (schmidtRank M) ↔
      FlatSchmidtSpectrum M := by
    rw [mutualInformation_eq_two_mul_entanglementEntropy_general M]
    constructor
    · intro h
      apply (entanglementEntropy_eq_log_schmidtRank_iff hM).mp
      linarith
    · intro h
      rw [(entanglementEntropy_eq_log_schmidtRank_iff hM).mpr h]
  constructor
  · intro heq
    have hlower : 2 * Real.log (schmidtRank M) ≤ mutualInformation M := by
      rw [← heq]
      exact phi_le_mutualInformation hpsi hn p
    have hupper : mutualInformation M ≤ 2 * Real.log (schmidtRank M) :=
      mutualInformation_le_two_log_schmidtRank hM
    have hflat : FlatSchmidtSpectrum M := hsat.mp (le_antisymm hupper hlower)
    refine ⟨hflat, fun q => ?_⟩
    rw [← heq]
    exact phi_le_mutualInformation hpsi hn q
  · rintro ⟨hflat, hmin⟩
    apply le_antisymm
    · exact le_trans (phi_le_mutualInformation hpsi hn p)
        (le_of_eq (hsat.mpr hflat))
    · exact le_phi hpsi hn hmin

#print axioms solution
