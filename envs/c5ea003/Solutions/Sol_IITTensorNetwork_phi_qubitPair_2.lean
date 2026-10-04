-- Prove2me | solution 2 for IITTensorNetwork.phi_qubitPair
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-21T13:54:02.752885+00:00
-- url     : https://prove2.me/submissions/1794d21c-d31e-4c67-96cd-016cc54d5a81

import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidtSpectrum
import Theorems.Thm_IITTensorNetwork_chainCutMatrix_qubitPairState
import Theorems.Thm_IITTensorNetwork_mutualInformation_eq_two_mul_entanglementEntropy
import Theorems.Thm_IITTensorNetwork_qubitPairState_normalized
import Theorems.Thm_IITTensorNetwork_vnEntropy_diagonal

open Finset Matrix
open scoped ComplexOrder

namespace IITTensorNetwork

private theorem phi_two_sites_inline {d : ℕ} {psi : (Fin 2 → Fin d) → ℂ}
    (hpsi : ∑ s, ‖psi s‖ ^ 2 = 1) :
    Phi hpsi (le_refl 2) = mutualInformation (chainCutMatrix psi 1 (by omega)) := by
  simp only [Phi, IntegratedInformation.Phi, chainCausalStructure]
  apply congrArg mutualInformation
  ext i j
  rfl

private theorem entanglementEntropy_schmidtDiag
    {α : Type*} [Fintype α] [DecidableEq α] (v : α → ℝ) :
    entanglementEntropy (schmidtDiag v) = ∑ i, Real.negMulLog (v i ^ 2) := by
  rw [entanglementEntropy]
  have hrho : rhoLeft (schmidtDiag v) = Matrix.diagonal (fun i => ((v i ^ 2 : ℝ) : ℂ)) := by
    rw [rhoLeft, schmidtDiag, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Pi.star_apply, pow_two]
  rw [hrho, vnEntropy_diagonal]

theorem phi_qubitPair {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    Phi (qubitPairState_normalized h) (le_refl 2) =
      2 * (Real.negMulLog (c ^ 2) + Real.negMulLog (s ^ 2)) := by
  rw [phi_two_sites_inline (qubitPairState_normalized h)]
  rw [chainCutMatrix_qubitPairState c s]
  rw [mutualInformation_eq_two_mul_entanglementEntropy]
  rw [entanglementEntropy_schmidtDiag]
  congr 1
  let e : (Fin 1 → Fin 2) ≃ Fin 2 := Equiv.funUnique (Fin 1) (Fin 2)
  rw [← e.symm.sum_comp (fun x => Real.negMulLog ((qubitPairCoeff c s x) ^ 2))]
  simp [e, qubitPairCoeff, Fin.sum_univ_two]

end IITTensorNetwork

theorem solution {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    IITTensorNetwork.Phi (IITTensorNetwork.qubitPairState_normalized h) (le_refl 2) =
      2 * (Real.negMulLog (c ^ 2) + Real.negMulLog (s ^ 2)) := by
  exact IITTensorNetwork.phi_qubitPair h

#print axioms IITTensorNetwork.phi_qubitPair
#print axioms solution
